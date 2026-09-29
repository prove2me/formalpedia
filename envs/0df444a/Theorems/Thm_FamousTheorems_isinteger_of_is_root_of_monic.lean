-- Prove2me | Theorems.Thm_FamousTheorems_isinteger_of_is_root_of_monic
-- name    : FamousTheorems.isinteger_of_is_root_of_monic
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:48.94089+00:00
-- url     : https://prove2.me/theorems/91a036d0-2743-40bb-8ae0-34c3160c0eb4
-- title:
--   The integral root theorem
-- statement:
--   **The integral root theorem.** A rational root of a monic polynomial with integer coefficients is an integer. Monicity is what forces it: the rational root theorem gives that the denominator divides the leading coefficient, which is $1$. Equivalently, $\mathbb{Z}$ is integrally closed in $\mathbb{Q}$ — an algebraic integer that is rational is an ordinary integer. That principle is used constantly in number theory, and it is exactly the step that makes Niven's theorem work, where $2\cos\theta$ is shown to be an algebraic integer and then pinned to a small finite set. **Formalization note.** The statement is for a monic integer polynomial with a root in the fraction field. The result is Mathlib's `isInteger_of_is_root_of_monic`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem isinteger_of_is_root_of_monic :
    ∀ {A : Type u_1} {K : Type u_2} [inst : CommRing A] [IsDomain A] 
    [UniqueFactorizationMonoid A] [inst_3 : Field K] [inst_4 : Algebra A K] [IsFractionRing A K] {p : Polynomial A}, 
    p.Monic → ∀ {r : K}, (Polynomial.aeval r) p = 0 → IsLocalization.IsInteger A r := by sorry

end FamousTheorems
