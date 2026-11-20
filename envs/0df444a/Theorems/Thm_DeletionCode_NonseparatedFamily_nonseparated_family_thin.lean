-- Prove2me | Theorems.Thm_DeletionCode_NonseparatedFamily_nonseparated_family_thin
-- name    : DeletionCode.NonseparatedFamily.nonseparated_family_thin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:58:02.043937+00:00
-- url     : https://prove2.me/theorems/48fa1f0f-9760-4e3e-9c85-a0bb8b4ea5a3
-- title:
--   Nonseparated Family: nonseparated family thin
-- statement:
--   The manuscript's existence-of-a-constant formulation of `lem:nonsep`.
--   The global paper assumption n >= L is explicit, and target uniqueness is absent.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L43-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/NonseparatedFamily.lean#L43-L52

import Definitions.Def_DeletionCode_ExceptionalPartnerCount
import Definitions.Def_DeletionCode_NonseparatedFamily
set_option autoImplicit true
open DeletionCode DeletionCode.NonseparatedFamily
open MeasureTheory Windows HeaderRecovery SignedSupport CircleHash CircleUniform ConflictGraphWitness
open ExceptionalProbability ExceptionalPartnerCount ExceptionalCountArithmetic

theorem DeletionCode.NonseparatedFamily.nonseparated_family_thin (t : ℕ) (ht : 2 ≤ t) :
    ∃ c : ℕ, 0 < c ∧ ∀ (n k Q : ℕ) (x : Bits n),
      KUnique (padBits x) n k → windowLength k ≤ n → 2 ≤ Q →
        (realWeights (Gram (windowLength k))
          {weights | FiniteConflictGraph.Exceptional t k
            (wordLabel Q (realWeightedHash weights)) x}).toReal ≤
          2 * (c : ℝ) * (n : ℝ) ^ (2 * t - 1) * (windowLength k : ℝ) / Q := by sorry
