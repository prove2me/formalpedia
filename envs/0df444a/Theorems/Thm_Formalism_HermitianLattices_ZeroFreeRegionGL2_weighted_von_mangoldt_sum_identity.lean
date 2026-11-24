-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_ZeroFreeRegionGL2_weighted_von_mangoldt_sum_identity
-- name    : Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_von_mangoldt_sum_identity
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:54.134982+00:00
-- url     : https://prove2.me/theorems/c123873f-4f5b-40a0-ac21-3f67620d782b
-- title:
--   Zero Free Region GL2: weighted von mangoldt sum identity
-- statement:
--   The Zero Free Region GL2 construction uses the weighted von mangoldt sum identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L227-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/WeightedVonMangoldtSumIdentity.lean#L227-L247

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2

theorem Formalism.HermitianLattices.ZeroFreeRegionGL2.weighted_von_mangoldt_sum_identity (a w : ℝ) (M : ℕ) (ha : 0 < a) (hw : 0 < w) (hM : ⌊a / w⌋₊ ≤ M) :
    w * (∑ n ∈ Icc 1 ⌊a / w⌋₊, Λ n * (a / w / n - 1)) = ∑ n ∈ Icc 1 M, Λ n * max (a / n - w) 0 := by sorry
