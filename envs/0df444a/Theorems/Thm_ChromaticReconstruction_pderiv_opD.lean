-- Prove2me | Theorems.Thm_ChromaticReconstruction_pderiv_opD
-- name    : ChromaticReconstruction.pderiv_opD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T12:43:05.049277+00:00
-- url     : https://prove2.me/theorems/36ef0837-d3ba-4096-aa70-dedc3bc9552e
-- title:
--   Chromatic Reconstruction: pderiv op D
-- statement:
--   The Chromatic Reconstruction construction uses the pderiv op D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L150-L181
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Uniform.lean#L150-L181

import Definitions.Def_RequestProject_LeafExtMaster
import Definitions.Def_RequestProject_CompStructure
import Definitions.Def_RequestProject_Uniform
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {V : Type*} [Fintype V]

theorem ChromaticReconstruction.pderiv_opD (q N r : ℕ) (hq : 2 ≤ q) (hrN : r < N) (hr : 1 ≤ r) (hqr : q * r - 1 ≠ 1)
    (f : MvPolynomial ℕ ℚ) :
    pderiv (q * r - 1) (opD q N f) = C (r : ℚ) * psiQ q (pderiv r f) := by sorry
