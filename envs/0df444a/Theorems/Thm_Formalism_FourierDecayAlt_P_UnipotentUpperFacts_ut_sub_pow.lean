-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentUpperFacts_ut_sub_pow
-- name    : Formalism.FourierDecayAlt.P.UnipotentUpperFacts.ut_sub_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:27:42.602857+00:00
-- url     : https://prove2.me/theorems/a965d6db-32b0-4d55-b6c0-e47a5922743a
-- title:
--   Unipotent Upper Facts: ut sub pow
-- statement:
--   The Unipotent Upper Facts construction uses the ut sub pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/UnipotentUpperFacts.lean#L48-L54

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

theorem Formalism.FourierDecayAlt.P.UnipotentUpperFacts.ut_sub_pow {m : ℕ} {u : Matrix (Fin m) (Fin m) ℂ} (hu : u ∈ C2.UTset m) : (u - 1) ^ m = 0 := by sorry
