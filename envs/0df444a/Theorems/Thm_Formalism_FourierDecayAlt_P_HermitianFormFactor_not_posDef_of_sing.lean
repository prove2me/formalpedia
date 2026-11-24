-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_not_posDef_of_sing
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.not_posDef_of_sing
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:15:07.418214+00:00
-- url     : https://prove2.me/theorems/94ada4dd-602e-4238-aef4-e8601334ca16
-- title:
--   Hermitian Form Factor: not pos Def of sing
-- statement:
--   The Hermitian Form Factor construction uses the not pos Def of sing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L608-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L608-L629

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.not_posDef_of_sing (M : Matrix Q Q ℂ) (n : Q → ℂ) (hn : n ≠ 0) (hM : Mᴴ *ᵥ n = 0) (j₀ : Q) (s : ℝ) (hs : s ≤ 0) :
    ¬ (Mᴴ * M + (s : ℂ) • Matrix.single j₀ j₀ (1 : ℂ)).PosDef := by sorry
