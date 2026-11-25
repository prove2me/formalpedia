-- Prove2me | Theorems.Thm_ChromaticReconstruction_theta_independent
-- name    : ChromaticReconstruction.theta_independent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T14:02:45.787812+00:00
-- url     : https://prove2.me/theorems/9e4d562a-897b-47e7-af38-9b416da196e1
-- title:
--   Chromatic Reconstruction: theta independent
-- statement:
--   **Lemma theta.** The polynomials `Θ_{ab}` indexed by feasible pairs are linearly independent;
--   in particular a nonnegative combination determines its coefficients.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L185-L243
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L185-L243

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.theta_independent {W : Multiset ℕ} (hW : ∀ x ∈ W, 2 ≤ x) (E1 E2 : Multiset (Sym2 ℕ))
    (hf : ∀ z ∈ E1 + E2, pairMS z ≤ W)
    (h : (E1.map (theta W)).sum = (E2.map (theta W)).sum) : E1 = E2 := by sorry
