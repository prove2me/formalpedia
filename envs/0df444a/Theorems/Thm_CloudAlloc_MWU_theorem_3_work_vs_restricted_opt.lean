-- Prove2me | Theorems.Thm_CloudAlloc_MWU_theorem_3_work_vs_restricted_opt
-- name    : CloudAlloc.MWU.theorem_3_work_vs_restricted_opt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:02.969133+00:00
-- url     : https://prove2.me/theorems/ce1be66c-0554-4ed3-ac9f-5e36125e8c24
-- title:
--   Theorem 3 (corrected: $\eta>0 \to 0<\eta\le 1/3$): work against $(1-4\varepsilon)$-allocations
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, SLAs $\beta\ge 0$ with $\sum_i\beta(i)\le 1$, nonnegative loads, and $h$ a run of Algorithm 1. For every time $t$ and every offline sequence $h^*_1,h^*_2,\dots$ of $(1-4\varepsilon)$-allocations ($h^*_\tau\ge 0$, $\sum_i h^*_\tau(i)\le 1-4\varepsilon$),
--
--   $$
--   \mathrm{work}_{h^*_1,\dots,h^*_t}-\mathrm{work}_{\mathrm{alg},t}\ \le\ 8\,\frac{N}{\varepsilon^2\eta}\ln(N/\varepsilon).
--   $$
--
--   Against a slightly handicapped dynamic benchmark, the algorithm loses only an additive constant independent of $t$; Theorem 1's work guarantee follows from it.
--
--   Differences from the source:
--   - correction: any ε > 0 and η > 0 with ε ≤ 1/10 → 0 < ε ≤ 1/10 and 0 < η ≤ 1/3; reason: counterexample N = 2, ε = 1/10, η = 10⁵, β = (1/2, 1/2), h_1 = (0.95, 0.05), L_1 = (0, 1): at t = 1 the allocation (0, 0.6) does 0.6, the algorithm 0.05, and 0.55 > 8N/(ε²η)·ln(N/ε) ≈ 0.048; 0 < η ≤ 1/3 is the range of Lemma 2 and Theorem 4
--   - generalization: the optimal offline sequence of (1 − 4ε)-allocations → every nonnegative sequence with Σ_i h*_τ(i) ≤ 1 − 4ε, compared over its first t steps; reason: an optimum exists and dominates every feasible sequence, so the statement specializes to the optimal one
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Theorem 3, p. 10 (proof pp. 11–12)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_totalWork

namespace CloudAlloc.MWU

/-- **Theorem 3 (corrected: `η > 0` → `0 < η ≤ 1/3`): work against `(1 − 4ε)`-allocations.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Theorem 3, p. 10 (proof pp. 11–12):
"Given loads `L1, . . . , LT`, for any `ε > 0` and `η > 0` such that `ε ≤ 1/10`, Algorithm 1 guarantees
`work_{h∗1,...,h∗t} − work_{alg,t} ≤ 8 N/(ε²η) ln(N/ε)`, for any time `1 ≤ t ≤ T`, where
`h∗1, . . . , h∗T` is the optimal offline sequence of `(1 − 4ε)`-allocations and
`work_{alg,t} = Σ_i Σ_{τ=1}^t wτ(i)` is the work done by Algorithm 1 until time `t`."

For a run of Algorithm 1 (standing hypotheses, `0 < η ≤ 1/3`), every time `t` and every offline
sequence of `(1 − 4ε)`-allocations (nonnegative, summing to at most `1 − 4ε` at each step), the work
that sequence does in the first `t` steps exceeds the algorithm's by at most `8N/(ε²η)·ln(N/ε)`.

**Formalization Note.** Lean time `t` is the paper's `t + 1`; `totalWork hs L t` is the work of `hs` in
paper steps `1, …, t`, with `hs`'s own queues on the same loads, from `Q_1 = 0`. The benchmark is any
`(1 − 4ε)`-allocation sequence, not only the optimal one; this is equivalent, since an optimum exists
and dominates every feasible sequence. `t = 0` is included (both sides are `0`). `ln` is `Real.log`.
**Correction.** As printed (any `η > 0`) the theorem is false: `N = 2`, `ε = 1/10`, `η = 10⁵`,
`β = (1/2, 1/2)`, `h_1 = (0.95, 0.05) ∈ Δ_ε`, `L_1 = (0, 1)`: at `t = 1` the allocation `(0, 0.6)`
does `0.6`, the algorithm `0.05`, and `0.55 > 8N/(ε²η)·ln(N/ε) ≈ 0.048`. The range is corrected to
`0 < η ≤ 1/3`, the range of Lemma 2 and Theorem 4, which contains Algorithm 1's input range. -/
theorem theorem_3_work_vs_restricted_opt {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ0 : ∀ i, 0 ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    ∀ (t : ℕ) (hs : ℕ → Fin N → ℝ),
      (∀ τ < t, (∀ i, 0 ≤ hs τ i) ∧ ∑ i, hs τ i ≤ 1 - 4 * ε) →
        totalWork hs L t - totalWork h L t ≤ 8 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε) := by sorry

end CloudAlloc.MWU
