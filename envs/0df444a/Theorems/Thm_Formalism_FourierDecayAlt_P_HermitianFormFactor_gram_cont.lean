-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_gram_cont
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_cont
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:56.630799+00:00
-- url     : https://prove2.me/theorems/c5238520-4c13-47cb-bd5e-76bcdfab21ea
-- title:
--   Hermitian Form Factor: gram cont
-- statement:
--   The Hermitian Form Factor construction uses the gram cont property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L577-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L577-L580

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HermitianFormFactor
variable {Q : Type} [Fintype Q] [DecidableEq Q]

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.gram_cont : Continuous (fun X : Q → Q → ℂ => (gram X : Q → Q → ℂ)) := by sorry
