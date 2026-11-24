-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_blk_pow
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.blk_pow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:41:28.638336+00:00
-- url     : https://prove2.me/theorems/44383de0-a177-4877-bba9-46c7490e9a5e
-- title:
--   Unipotent Upper Facts: blk pow
-- statement:
--   The Unipotent Upper Facts construction uses the blk pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L39-L44

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FixedPointsGramVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.UnipotentUpperFacts
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector
variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.blk_pow {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix p p ℂ) (D : Matrix q q ℂ) (m : ℕ) :
    (Matrix.fromBlocks A 0 0 D) ^ m = Matrix.fromBlocks (A ^ m) 0 0 (D ^ m) := by sorry
