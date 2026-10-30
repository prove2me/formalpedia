-- Prove2me | Theorems.Thm_CloudAlloc_MWU_claim_3_2_low_utilization
-- name    : CloudAlloc.MWU.claim_3_2_low_utilization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:42:07.289847+00:00
-- url     : https://prove2.me/theorems/7702ab52-6219-4485-8e93-de21b905a735
-- title:
--   Claim 3.2: few low-utilization steps after $s^\star$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta\ge 0$ with $\sum_i\beta(i)\le 1$, nonnegative loads, and $h$ a run of Algorithm 1. Let $c=\varepsilon\eta/(4N)$, $\tilde s=\ln(N/\varepsilon)/(\varepsilon c)$, a horizon $T$, and let $s^\star$ be the largest integer $0\le s\le T$ with
--
--   $$
--   \sum_{t=1}^{s}\sum_i L_t(i)\ \le\ \sum_{t=1}^{s+\tilde s}\sum_i w_t(i). \tag{7}
--   $$
--
--   Then:
--
--   1. for every block $B=[r,r+\tilde s)$ inside the horizon with $r>s^\star$, the set $B'=\{t\in B:\sum_{j\in A_t}h_t(j)\le 1-\varepsilon\}$ of low-utilization steps satisfies $|B'|\le 4\varepsilon\tilde s$;
--   2. $\displaystyle\sum_{t=s^\star+1}^T\sum_i w_t(i)\ \ge\ (1-4\varepsilon)(T-s^\star)-\tilde s$.
--
--   Together with Proposition 2 at $4\varepsilon$ and the choice of $s^\star$, this gives Theorem 3.
--
--   Differences from the source:
--   - reading: real sum limits Σ_{t=1}^{s+s̃} and the block B = [r, r + s̃) → integer points: t ≤ s + ⌊s̃⌋₊, B = the integers τ with r ≤ τ < r + s̃; reason: s̃ is real; sums and blocks range over integer times
--   - reading: s⋆ the maximum non-negative integer with (7); blocks of time → s⋆ maximal over 0 ≤ s ≤ T; the block lies inside [1, T]; reason: the proof of Claim 3.2 (p. 29) partitions [s⋆ + 1, T] into such blocks
--   - reading: w_t(i) = min{h_t(i), L_t(i) + Q_t(i)} (p. 3) and the remark "h_t(i) = w_t(i) for all active users" (p. 8) → work is min{h, L + Q}; nothing like w = h for active users is assumed; reason: the p. 3 definition is binding; the p. 8 remark is false when L_t(i) + Q_t(i) < h_t(i)
--   - generalization: η in Algorithm 1's input range 0 < η < 1/3 (no η range printed in this statement) → 0 < η ≤ 1/3; reason: the range printed in Lemma 2 and Theorem 4; it contains Algorithm 1's input range, so the statement specializes to it
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Claim 3.2, p. 12 (proof in Appendix B, p. 29)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_work

namespace CloudAlloc.MWU

/-- **Claim 3.2: few low-utilization steps after `s⋆`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Claim 3.2, p. 12 (proof in Appendix B, p. 29):
"Let `B = [r, r + s̃)` with `r > s⋆` be a consecutive block of `s̃` timesteps and let
`B′ = {t ∈ B : Σ_{j∈At} ht(j) ≤ 1−ε}` be the time steps in `B` with low utilization. Then
`|B′| ≤ 4εs̃` and therefore, `Σ_{t=s⋆+1}^T Σ_i wt(i) ≥ (1 − 4ε)(T − s⋆) − s̃`."
Here `s̃ = ln(N/ε)/(εc)`, `c = εη/(4N)` and `s⋆` is the largest `s ≥ 0` with
`Σ_{t=1}^s Σ_i Lt(i) ≤ Σ_{t=1}^{s+s̃} Σ_i wt(i)` (7) (p. 12).

For a run of Algorithm 1 (standing hypotheses), a horizon `T` and `s⋆` as above: (1) every block
`[r, r + s̃)` inside the horizon starting after `s⋆` contains at most `4εs̃` steps at which the
active users hold at most `1 − ε` in total; (2) the work done after `s⋆` is at least
`(1 − 4ε)(T − s⋆) − s̃`.

**Formalization Note.** Lean time `t` is the paper's `t + 1` (`h t` = `h_{t+1}`, `queue h L t` =
`Q_{t+1}`, `work h L t` = `w_{t+1}`). Lean `s⋆ ≤ r` is the paper's `r > s⋆` (stated as printed); the
block is the integers `τ` with `r ≤ τ < r + s̃` (real `s̃`, literal reading) inside `[0, T)`, and the
block is assumed to lie in the horizon (`r + s̃ ≤ T` in Lean time), as the proof partitions
`[s⋆ + 1, T]` into such blocks (p. 29). Active users are those with `0 < queue h L τ j`.
`Σ_{t=s⋆+1}^T` is `Finset.Ico s⋆ T`; `T − s⋆` is a real subtraction (`s⋆ ≤ T` by its definition).
Real sum limits in (7) are read as `s + ⌊s̃⌋`. The η range is `0 < η ≤ 1/3` (Lemma 2, Theorem 4).
Work is `min{h, L + Q}` as defined on p. 3; nothing like "`w = h` for active users" is assumed. -/
theorem claim_3_2_low_utilization {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h)
    (T sstar : ℕ) :
    let c := ε * η / (4 * (N : ℝ))
    let st := Real.log ((N : ℝ) / ε) / (ε * c)
    let S := ⌊st⌋₊
    IsGreatest {s : ℕ | s ≤ T ∧ ∑ t ∈ Finset.range s, ∑ i, L t i ≤
        ∑ t ∈ Finset.range (s + S), ∑ i, work h L t i} sstar →
      (∀ r : ℕ, sstar ≤ r → (r : ℝ) + st ≤ T →
          ((((Finset.range T).filter (fun τ => r ≤ τ ∧ (τ : ℝ) < r + st)).filter
              (fun τ => ∑ j ∈ Finset.univ.filter (fun j => 0 < queue h L τ j), h τ j ≤ 1 - ε)).card
              : ℝ) ≤ 4 * ε * st) ∧
        (1 - 4 * ε) * ((T : ℝ) - sstar) - st ≤ ∑ t ∈ Finset.Ico sstar T, ∑ i, work h L t i := by sorry

end CloudAlloc.MWU
