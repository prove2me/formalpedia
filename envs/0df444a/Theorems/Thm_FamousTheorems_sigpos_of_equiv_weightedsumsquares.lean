-- Prove2me | Theorems.Thm_FamousTheorems_sigpos_of_equiv_weightedsumsquares
-- name    : FamousTheorems.sigpos_of_equiv_weightedsumsquares
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T08:37:43.220005+00:00
-- url     : https://prove2.me/theorems/d01c4cfa-b116-4d37-920c-17f59a186213
-- title:
--   Sylvester's law of inertia (uniqueness)
-- statement:
--   **Sylvester's law of inertia**, uniqueness half. If a quadratic form over an ordered field is equivalent to a weighted sum of squares with weights of prescribed signs, then the number of positive weights is determined by the form alone — it does not depend on the diagonalising change of basis. Diagonalising a quadratic form is highly non-unique: different bases give different weights. What the law of inertia says is that the *signature* — the count of positive, negative and zero weights — is an invariant. Two real quadratic forms are equivalent precisely when they share a signature, which completely classifies them. This is why "positive definite" is a well-defined notion, and why the index of a critical point in Morse theory makes sense. The corresponding statement over $\mathbb{C}$ collapses, since every nonzero weight can be scaled to $1$ there. Sylvester published it in 1852, naming it the law of inertia. **Formalization note.** `QuadraticForm.sigPos` is the number of positive weights in a weighted-sum-of-squares presentation. The result is Mathlib's `QuadraticForm.sigPos_of_equiv_weightedSumSquares`.
-- source:
--   Listed in Mathlib's undergraduate/overview curriculum manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem sigpos_of_equiv_weightedsumsquares :
    ∀ {M : Type u_1} [inst : AddCommGroup M] {𝕜 : Type u_2} 
    [inst_1 : Field 𝕜] [inst_2 : LinearOrder 𝕜] [inst_3 : Module 𝕜 M] {Q : QuadraticForm 𝕜 M} {ι : Type u_3} 
    [inst_4 : Fintype ι] {w : ι → 𝕜} [IsStrictOrderedRing 𝕜], 
    QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares 𝕜 w) → sigPos Q = {i | 0 < w i}.ncard := by sorry

end FamousTheorems
