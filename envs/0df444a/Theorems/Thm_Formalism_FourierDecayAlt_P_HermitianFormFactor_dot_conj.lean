-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_dot_conj
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.dot_conj
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:58:26.729353+00:00
-- url     : https://prove2.me/theorems/9e4a9020-476b-4924-81d8-2e9898a515e0
-- title:
--   Hermitian Form Factor: dot conj
-- statement:
--   The Hermitian Form Factor construction uses the dot conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L573-L575
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L573-L575

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.dot_conj (a b : Q → ℂ) : star a ⬝ᵥ b = star (star b ⬝ᵥ a) := by sorry
