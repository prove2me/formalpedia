-- Prove2me | Theorems.Thm_ChromaticReconstruction_X_mul_fP
-- name    : ChromaticReconstruction.X_mul_fP
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T13:49:55.074913+00:00
-- url     : https://prove2.me/theorems/a79ced15-c29e-4445-9357-2104f59ab388
-- title:
--   Chromatic Reconstruction: X mul f P
-- statement:
--   The Chromatic Reconstruction construction uses the X mul f P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L44-L49
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L44-L49

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.X_mul_fP (r : ℕ) (V : Multiset ℕ) :
    X r * fP V = ∑ c ∈ bigWeights V, C (((c - 1) * V.count c : ℕ) : ℚ) * mono (r ::ₘ lowerAt V c) := by sorry
