-- Prove2me | Theorems.Thm_FamousTheorems_continuous_of_uniform_approx_of_continuous
-- name    : FamousTheorems.continuous_of_uniform_approx_of_continuous
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:26:09.734679+00:00
-- url     : https://prove2.me/theorems/9d10902a-fe7e-4685-8f19-adfc6372db1a
-- title:
--   Uniform limits of continuous functions are continuous
-- statement:
--   **The uniform limit theorem.** If a function can be approximated uniformly, to arbitrary accuracy, by continuous functions, then it is itself continuous. Uniformity is essential and is precisely what pointwise convergence lacks: $x^n$ on $[0,1]$ is a pointwise limit of continuous functions with a discontinuous limit, and the failure is that the rate of convergence degrades as $x \to 1$. The proof is the $\varepsilon/3$ argument — approximate within $\varepsilon/3$, use continuity of the approximant on a neighbourhood, and pay $\varepsilon/3$ twice more to return. The theorem is what makes $C(X)$ complete in the sup norm, and hence what allows Banach-space methods to be applied to spaces of continuous functions; it is also the reason Weierstrass approximation produces continuous limits and the basis for defining functions by uniformly convergent series. **Formalization note.** The hypothesis is stated as approximation within every entourage of the uniformity rather than by a sequence, so it covers nets and filters uniformly. The result is Mathlib's `continuous_of_uniform_approx_of_continuous`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem continuous_of_uniform_approx_of_continuous :
    ∀ {α : Type u_1} {β : Type u_2} [inst : TopologicalSpace α] 
    [inst_1 : UniformSpace β] {f : α → β}, 
    (∀ u ∈ uniformity β, ∃ F, Continuous F ∧ ∀ (y : α), (f y, F y) ∈ u) → Continuous f := by sorry

end FamousTheorems
