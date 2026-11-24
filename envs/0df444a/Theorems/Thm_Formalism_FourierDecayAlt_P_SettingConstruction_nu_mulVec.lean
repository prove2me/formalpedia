-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_nu_mulVec
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.nu_mulVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:22:27.811854+00:00
-- url     : https://prove2.me/theorems/761e33df-80ba-4503-98bd-7576653d4cca
-- title:
--   Setting Construction: nu mul Vec
-- statement:
--   The Setting Construction construction uses the nu mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L154-L160

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingConstruction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SettingConstruction
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable (k : ℕ)

theorem Formalism.FourierDecayAlt.P.SettingConstruction.nu_mulVec (w s : ℂ) (x : Fin (k + 1) → ℂ) :
    nu k w s *ᵥ x = x + x 0 • ((star w - 1) • Pi.single 0 1 + s • Pi.single (Fin.last k) 1) +
      x (Fin.last k) • (s • Pi.single 0 1 + (w - 1) • Pi.single (Fin.last k) 1) := by sorry
