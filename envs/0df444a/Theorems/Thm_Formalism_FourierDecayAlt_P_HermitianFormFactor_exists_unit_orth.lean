-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormFactor_exists_unit_orth
-- name    : Formalism.FourierDecayAlt.P.HermitianFormFactor.exists_unit_orth
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:14:52.929776+00:00
-- url     : https://prove2.me/theorems/0dde4b33-a30f-46d5-9a6d-c8d2cbb59386
-- title:
--   Hermitian Form Factor: exists unit orth
-- statement:
--   The Hermitian Form Factor construction uses the exists unit orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L683-L715
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HermitianFormFactor.lean#L683-L715

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

theorem Formalism.FourierDecayAlt.P.HermitianFormFactor.exists_unit_orth (X : Q → Q → ℂ) (j₀ : Q) :
    ∃ n : Q → ℂ, star n ⬝ᵥ n = 1 ∧ ∀ j, j ≠ j₀ → star n ⬝ᵥ X j = 0 := by sorry
