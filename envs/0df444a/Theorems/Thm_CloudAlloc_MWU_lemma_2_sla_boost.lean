-- Prove2me | Theorems.Thm_CloudAlloc_MWU_lemma_2_sla_boost
-- name    : CloudAlloc.MWU.lemma_2_sla_boost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:44:33.276831+00:00
-- url     : https://prove2.me/theorems/b7386cc8-b8dd-4f50-9f8e-b5adabd451e1
-- title:
--   Lemma 2: active users below their SLA are boosted by $1+c'$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs with $\beta(j)\ge 2\varepsilon/N$ for all users and $\sum_j\beta(j)\le 1$, nonnegative loads, and $h$ a run of Algorithm 1. Let $\lambda=\varepsilon^2/(8N)$ and $c'=\varepsilon\eta\lambda/(2N)$. Then every active user $i$ with $h_t(i)<\beta(i)$ satisfies
--
--   $$
--   h_{t+1}(i)\ \ge\ h_t(i)\,(1+c').
--   $$
--
--   A busy user below its SLA climbs geometrically towards it; this is the engine of Theorem 4.
--
--   Differences from the source:
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Lemma 2, p. 13 (proof in Appendix B, pp. 29–30)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run

namespace CloudAlloc.MWU

/-- **Lemma 2: active users below their SLA are boosted.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Lemma 2, p. 13 (proof in Appendix B, pp. 29–30):
"Assume `ε ≤ 1/10`, `η ≤ 1/3` and `β(i) ≥ 2ε/N` for all users. Then for any `i ∈ A¹t`, Algorithm 1
guarantees `ht+1(i) ≥ ht(i)(1 + c′)`, where `c′ = εηλ/(2N)`", with `λ = ε²/(8N)` (p. 13).

For a run of Algorithm 1 with `N ≥ 2`, `0 < ε ≤ 1/10`, `0 < η ≤ 1/3`, SLAs `β(j) ≥ 2ε/N` with
`Σβ ≤ 1` and nonnegative loads: every active user whose allocation is strictly below its SLA has its
allocation multiplied by at least `1 + c′` in the next step.

**Formalization Note.** Lean time `t` is the paper's `t + 1`. `i ∈ A¹_t` is `0 < queue h L t i` and
`h t i < β i`. `0 < ε` and `0 < η` are Algorithm 1's input (p. 9); `N ≥ 2` (p. 8) and `Σβ ≤ 1` (p. 3)
are standing. The proof (p. 29) writes `Σ_j β(j) = 1`; the standing `Σβ ≤ 1` is kept, not
strengthened. `β ≥ 0` is implied by `β(j) ≥ 2ε/N` and not stated separately. -/
theorem lemma_2_sla_boost {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, 2 * ε / N ≤ β j) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let lam := ε ^ 2 / (8 * (N : ℝ))
    let c' := ε * η * lam / (2 * (N : ℝ))
    ∀ t i, 0 < queue h L t i → h t i < β i → h t i * (1 + c') ≤ h (t + 1) i := by sorry

end CloudAlloc.MWU
