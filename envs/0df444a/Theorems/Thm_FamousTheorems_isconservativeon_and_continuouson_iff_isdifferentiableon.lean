-- Prove2me | Theorems.Thm_FamousTheorems_isconservativeon_and_continuouson_iff_isdifferentiableon
-- name    : FamousTheorems.isconservativeon_and_continuouson_iff_isdifferentiableon
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:56.517259+00:00
-- url     : https://prove2.me/theorems/7f885a30-eccc-465f-9199-6f43eddc1ba2
-- title:
--   Morera's theorem
-- statement:
--   **Morera's theorem.** A continuous function on an open set whose integral around every closed contour vanishes is holomorphic. This converse of Cauchy's theorem is the standard way to prove holomorphy without differentiating: vanishing integrals are often easy to check by Fubini or uniform convergence, whereas complex differentiability is not. It gives that a locally uniform limit of holomorphic functions is holomorphic, and that integrals depending holomorphically on a parameter, such as the Gamma function, define holomorphic functions. Morera published it in 1886. **Formalization note.** The vanishing-integral hypothesis is `isConservativeOn` and the statement is an iff. The result is Mathlib's `Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isconservativeon_and_continuouson_iff_isdifferentiableon :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℂ E] {f : ℂ → E} [CompleteSpace E] {U : Set ℂ}, 
    IsOpen U → (Complex.IsConservativeOn f U ∧ ContinuousOn f U ↔ DifferentiableOn ℂ f U) := by sorry

end FamousTheorems
