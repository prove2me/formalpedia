-- Prove2me | Theorems.Thm_CrossLayerControl_ECCA_lemma_4_3
-- name    : CrossLayerControl.ECCA.lemma_4_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-30T02:37:56.642651+00:00
-- url     : https://prove2.me/theorems/5c2ee117-5a51-4f2c-960d-024c2cdedee1
-- title:
--   Lemma 4.3 (one-step square bound for a queue)
-- statement:
--   If $W,U,\mu,A$ are nonnegative real numbers and
--   $$W\le\max[U-\mu,0]+A,$$
--   then
--   $$W^2\le U^2+\mu^2+A^2-2U(\mu-A).$$
--
--   Applied with $W=U(t+1)$, it bounds the change of $U(t)^2$ over one slot of the queue law $U(t+1)=\max[U(t)-\mu(t),0]+A(t)$, which is the source of the constant $B$ in drift bounds.
--
--   Differences from the source:
--   - encoding: the lemma's variable V → W; reason: V is the control parameter of ECCA elsewhere in the mission; renaming changes no instance
-- source:
--   Georgiadis, Neely, Tassiulas, Resource Allocation and Cross-Layer Control in Wireless Networks, Found. Trends Netw. 1(1) (2006), doi:10.1561/1300000001, Lemma 4.3, pp. 52–53

import Mathlib

namespace CrossLayerControl.ECCA

/-- **Lemma 4.3 (the one-step square bound for a queue).**
Georgiadis, Neely, Tassiulas, *Resource Allocation and Cross-Layer Control in Wireless Networks*,
Found. Trends Netw. 1(1) (2006), Lemma 4.3, pp. 52–53: "If V,U,µ,A are nonnegative real numbers and
V ≤ max[U − µ,0] + A, then V² ≤ U² + µ² + A² − 2U(µ − A)."

For nonnegative reals `W`, `U`, `μ`, `A` with `W ≤ max (U − μ) 0 + A`,
`W² ≤ U² + μ² + A² − 2U(μ − A)`.

**Formalization Note.** The lemma's `V` (a next-slot backlog) is renamed `W`, since `V` is the
control parameter of ECCA elsewhere in this development. -/
theorem lemma_4_3 (W U μ A : ℝ) (hW : 0 ≤ W) (hU : 0 ≤ U) (hμ : 0 ≤ μ) (hA : 0 ≤ A)
    (h : W ≤ max (U - μ) 0 + A) :
    W ^ 2 ≤ U ^ 2 + μ ^ 2 + A ^ 2 - 2 * U * (μ - A) := by sorry

end CrossLayerControl.ECCA
