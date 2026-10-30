-- Prove2me | Theorems.Thm_CloudAlloc_MWU_claim_3_1_busy_user
-- name    : CloudAlloc.MWU.claim_3_1_busy_user
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:41:18.489159+00:00
-- url     : https://prove2.me/theorems/2070964b-b11b-4065-b1ff-c8203790b3a1
-- title:
--   Claim 3.1 (corrected: $r>s^\star \to r>s^\star+1$): a busy user on every late block
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta\ge 0$ with $\sum_i\beta(i)\le 1$, nonnegative loads, and $h$ a run of Algorithm 1. Let $c=\varepsilon\eta/(4N)$, $\tilde s=\ln(N/\varepsilon)/(\varepsilon c)$, a horizon $T$, and let $s^\star$ be the largest integer $0\le s\le T$ with
--
--   $$
--   \sum_{t=1}^{s}\sum_i L_t(i)\ \le\ \sum_{t=1}^{s+\tilde s}\sum_i w_t(i). \tag{7}
--   $$
--
--   Then for every block of times $[r,r+\tilde s]$ inside $[1,T]$ with $r>s^\star+1$ there is a user $i$ whose queue is non-empty at every time of the block: $Q_{r'}(i)>0$ for all integers $r'\in[r,r+\tilde s]$.
--
--   After $s^\star$ the algorithm never lets all users idle for long; this feeds the utilization count of Claim 3.2.
--
--   Differences from the source:
--   - correction: r > s⋆ → r > s⋆ + 1 (Lean: sstar < r); reason: counterexample N = 2, ε = 1/10, η = 1/4, β = (1/2, 1/2), h_1 = (1/2, 1/2), L_1 = (10⁷, 0), L_t = 0 for t ≥ 2, T = 10⁵: s⋆ = 0, but every queue is empty at t = 1, so the block [1, 1 + s̃] has no busy user; the proof's equality for an empty queue at r′ holds only up to r′ − 1
--   - reading: real sum limits Σ_{t=1}^{s+s̃} and blocks [r, r + s̃] → integer points: t ≤ s + ⌊s̃⌋₊, block {r, …, r + ⌊s̃⌋₊}; reason: s̃ is real; sums and blocks range over integer times
--   - reading: s⋆ the maximum non-negative integer with (7); blocks of time → s⋆ maximal over 0 ≤ s ≤ T; the block lies inside [1, T]; reason: the proof of Claim 3.2 (p. 29) partitions [s⋆ + 1, T] into such blocks
--   - generalization: η in Algorithm 1's input range 0 < η < 1/3 (no η range printed in this statement) → 0 < η ≤ 1/3; reason: the range printed in Lemma 2 and Theorem 4; it contains Algorithm 1's input range, so the statement specializes to it
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, proof of Theorem 3, Claim 3.1 and display (7), p. 12

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_work

namespace CloudAlloc.MWU

/-- **Claim 3.1 (corrected: `r > s⋆` → `r > s⋆ + 1`): a busy user on every late block.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, proof of Theorem 3, Claim 3.1, p. 12:
"Let `s̃ = ln(N/ε)/(εc)`, where `c` is defined in Lemma 1. Now, pick `s⋆` to be the maximum
non-negative integer `s` (including 0) such that `Σ_{t=1}^s Σ_i Lt(i) ≤ Σ_{t=1}^{s+s̃} Σ_i wt(i)` (7).
Claim 3.1 Consider any block of time `[r, r + s̃]` where `r > s⋆`; then there exists a user `i` such
that `Mi,r′ = 1` for all `r′ ∈ [r, r + s̃]`", with `M_{i,t} = 1` iff `Q_t(i) > 0` (p. 12).

For a run of Algorithm 1 (standing hypotheses), `c = εη/(4N)`, `s̃ = ln(N/ε)/(εc)`, a horizon `T`
and `s⋆` the largest `s ∈ {0, …, T}` satisfying (7): for every block `[r, r + s̃]` inside `[1, T]`
that starts after `s⋆ + 1`, some user's queue is non-empty at every time of the block.

**Formalization Note.** Lean time `t` is the paper's `t + 1` (`queue h L t` = `Q_{t+1}`), so the Lean
block `[r, r + ⌊s̃⌋]` is the paper's `[r + 1, r + 1 + s̃]`; Lean `s⋆ < r` is paper `r > s⋆ + 1`.
Real sum limits are read literally: `Σ_{t=1}^{s+s̃}` runs over `t ≤ s + ⌊s̃⌋`. `s⋆` is the maximum
over `0 ≤ s ≤ T` and the block lies inside `[1, T]` (Lean `r + ⌊s̃⌋ < T`), as in the proof of Claim
3.2 (p. 29). The η range is `0 < η ≤ 1/3` (Lemma 2, Theorem 4).
**Correction.** As printed (`r > s⋆`, i.e. the block may start at `s⋆ + 1`) the claim is false:
`N = 2`, `ε = 1/10`, `η = 1/4`, `β = (1/2, 1/2)`, `h_1 = (1/2, 1/2)`, `L_1 = (10⁷, 0)`, `L_t = 0`
for `t ≥ 2`, `T = 10⁵` give `s⋆ = 0` while every queue is empty at `t = 1` (`Q_1 = 0`). The proof's
equality `Σ_{t≤r′} w_t(i) = Σ_{t≤r′} L_t(i)` for an empty queue at `r′` holds only up to `r′ − 1`;
with `r > s⋆ + 1` the printed argument goes through. -/
theorem claim_3_1_busy_user {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
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
      ∀ r : ℕ, sstar < r → r + S < T →
        ∃ i, ∀ r' ∈ Finset.Icc r (r + S), 0 < queue h L r' i := by sorry

end CloudAlloc.MWU
