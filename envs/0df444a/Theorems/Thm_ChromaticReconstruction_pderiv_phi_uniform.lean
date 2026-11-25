-- Prove2me | Theorems.Thm_ChromaticReconstruction_pderiv_phi_uniform
-- name    : ChromaticReconstruction.pderiv_phi_uniform
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:34:56.815026+00:00
-- url     : https://prove2.me/theorems/e6a3a9c1-63aa-4f2c-8923-ec98762dff89
-- title:
--   Chromatic Reconstruction: pderiv phi uniform
-- statement:
--   The Chromatic Reconstruction construction uses the pderiv phi uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L45-L50
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theorem2.lean#L45-L50

import Definitions.Def_RequestProject_ChromCoeff
import Definitions.Def_RequestProject_Theorem2
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V W : Type*} [Fintype V] [Fintype W]

theorem ChromaticReconstruction.pderiv_phi_uniform (q N r : ℕ) (hq : 2 ≤ q) (G : SimpleGraph V) (hN : Fintype.card V < N)
    (hrN : r < N) (hr : 1 ≤ r) (hqr : q * r - 1 ≠ 1) :
    pderiv (q * r - 1) (phi (uniformLeafExt q G)) =
      cFactor q (Fintype.card V) • (C (r : ℚ) * psiQ q (pderiv r (chromSymm G))) := by sorry
