-- Prove2me | Theorems.Thm_ChromaticReconstruction_coeff_thetaAB
-- name    : ChromaticReconstruction.coeff_thetaAB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:39:24.385575+00:00
-- url     : https://prove2.me/theorems/272fbf38-74d9-4af4-8dc3-69495a7ee68a
-- title:
--   Chromatic Reconstruction: coeff theta AB
-- statement:
--   The Chromatic Reconstruction construction uses the coeff theta AB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L130-L141
-- source:
--   https://github.com/sawan201/First-Derivative-CSF-Reconstruction-for-Proper-Trees/blob/2827a80aba46196bb8a2a25760df548bef0f3e6d/RequestProject/Theta.lean#L130-L141

import Definitions.Def_RequestProject_RecoverP
import Definitions.Def_RequestProject_Theta
set_option autoImplicit true
open MvPolynomial Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction

theorem ChromaticReconstruction.coeff_thetaAB (W : Multiset ℕ) (c d : ℕ) (ν : Multiset ℕ) :
    coeff (Multiset.toFinsupp ν) (thetaAB W c d) =
      (if (c + d - 1) ::ₘ (W - {c, d}) = ν then ((c + d - 2 : ℕ) : ℚ) else 0) +
      ∑ r ∈ bigWeights (W - {c, d}), if (c + d) ::ₘ lowerAt (W - {c, d}) r = ν then
        (((r - 1) * (W - {c, d}).count r : ℕ) : ℚ) else 0 := by sorry
