-- Prove2me | Theorems.Thm_DeletionCode_ExceptionalProbability_spectrum_difference_ne_zero
-- name    : DeletionCode.ExceptionalProbability.spectrum_difference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:57.374023+00:00
-- url     : https://prove2.me/theorems/e117fc23-f1ba-43c0-b1c9-cdb6c0982685
-- title:
--   Exceptional Probability: spectrum difference ne zero
-- statement:
--   Actual finite-word spectrum injectivity requires uniqueness only of x.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L53-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ExceptionalProbability.lean#L53-L68

import Definitions.Def_DeletionCode_RandomHash
import Definitions.Def_DeletionCode_ConflictGraphWitness
import Definitions.Def_DeletionCode_SpectrumPath
import Definitions.Def_DeletionCode_ExceptionalProbability
set_option autoImplicit true
open DeletionCode DeletionCode.ExceptionalProbability
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform
open ConflictGraphWitness
open scoped BigOperators
variable {n : ℕ}

theorem DeletionCode.ExceptionalProbability.spectrum_difference_ne_zero (k : ℕ) (x y : Bits n)
    (hx : KUnique (padBits x) n k) (hn : windowLength k ≤ n) (hxy : x ≠ y) :
    spectrum k y - spectrum k x ≠ 0 := by sorry
