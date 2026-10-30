-- Prove2me | Theorems.Thm_CloudAlloc_MWU_proposition_2_lp_value
-- name    : CloudAlloc.MWU.proposition_2_lp_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:40:25.86077+00:00
-- url     : https://prove2.me/theorems/f81d7813-c257-414d-baa0-5458f98b522e
-- title:
--   Proposition 2: value of the offline LP $(P_\varepsilon)$
-- statement:
--   Let $0<\varepsilon<1$, a horizon $T$ and nonnegative loads $L_1,\dots,L_T\in\mathbb R^N_{\ge 0}$. Consider the linear program
--
--   $$
--   (P_\varepsilon)\quad \max \sum_{i=1}^N\sum_{t=1}^T w_t(i)\quad\text{s.t.}\quad \sum_{s=1}^t w_s(i)\le\sum_{s=1}^t L_s(i)\ \ (\forall t,i),\qquad \sum_{i=1}^N w_t(i)\le 1-\varepsilon\ \ (\forall t),\qquad w_t\ge 0 .
--   $$
--
--   Its maximum is attained and equals
--
--   $$
--   v_{P_\varepsilon}=\min_{0\le t\le T}\Big(\sum_{s=1}^t\sum_i L_s(i)+(1-\varepsilon)(T-t)\Big).
--   $$
--
--   The LP bounds the work any $(1-\varepsilon)$-allocation can do; Theorem 3 uses it at $4\varepsilon$ through weak duality.
--
--   Differences from the source:
--   - encoding: v_{P_ε}, the optimal value of (P_ε) → IsGreatest of the set of objective values of feasible w; reason: states attainment and the value; (P_ε) is feasible and bounded (p. 11)
--   - encoding: constraints for t = 1, …, T and Σ_{s=1}^t → constraints for Lean t < T with Finset.range (t + 1); reason: 0-based indexing; same constraints
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Proposition 2 and Figure 2, p. 11 (proof in Appendix B, p. 27)

import Mathlib

namespace CloudAlloc.MWU

/-- **Proposition 2: the value of the offline LP `(P_ε)`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Proposition 2, p. 11 (proof in Appendix B, p. 27):
"`vPε = min_{0≤t≤T} (Σ_{s=1}^t Σ_i Ls(i) + (1 − ε)(T − t))`",
where `(P_ε)` (Figure 2, p. 11) is "`max Σ_{i=1}^N Σ_{t=1}^T wt(i)` s.t. `∀t, i Σ_{s=1}^t ws(i) ≤
Σ_{s=1}^t Ls(i)` (1); `∀t Σ_{i=1}^N wt(i) ≤ 1 − ε` (2); `∀t wt ≥ 0` (3)".

For `0 < ε < 1`, a horizon `T` and nonnegative loads `L`, the maximum of the total work
`Σ_{t=1}^T Σ_i w_t(i)` over all work patterns satisfying (1)–(3) is attained and equals
`min_{0≤t≤T} (Σ_{s=1}^t Σ_i L_s(i) + (1 − ε)(T − t))`.

**Formalization Note.** Lean time `t` is the paper's `t + 1`: the constraints are imposed for
`t < T`, and `Finset.range (t + 1)` is the paper's `s = 1, …, t + 1`. The value `v_{P_ε}` is stated
as a greatest element of the set of objective values (`IsGreatest`), so the optimum is attained and no
`sSup` default value can occur. Values of `w` after time `T` do not enter. `T − t` is a real
subtraction. -/
theorem proposition_2_lp_value {N : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℕ)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) :
    IsGreatest
      ((fun w : ℕ → Fin N → ℝ => ∑ t ∈ Finset.range T, ∑ i, w t i) ''
        {w | (∀ t < T, ∀ i, ∑ s ∈ Finset.range (t + 1), w s i ≤ ∑ s ∈ Finset.range (t + 1), L s i) ∧
          (∀ t < T, ∑ i, w t i ≤ 1 - ε) ∧ (∀ t < T, ∀ i, 0 ≤ w t i)})
      ((Finset.range (T + 1)).inf' ⟨0, Finset.mem_range.mpr (Nat.succ_pos T)⟩
        (fun t => ∑ s ∈ Finset.range t, ∑ i, L s i + (1 - ε) * ((T : ℝ) - t))) := by sorry

end CloudAlloc.MWU
