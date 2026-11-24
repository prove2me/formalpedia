-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SettingConstruction_herm_single
-- name    : Formalism.FourierDecayAlt.P.SettingConstruction.herm_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:52:59.319802+00:00
-- url     : https://prove2.me/theorems/1ff51fa7-6559-498e-9e59-e6307a4f7d7e
-- title:
--   Setting Construction: herm single
-- statement:
--   The Setting Construction construction uses the herm single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L61-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SettingConstruction.lean#L61-L62

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
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)
variable [DecidableEq ι]

theorem Formalism.FourierDecayAlt.P.SettingConstruction.herm_single (i j : ι) : herm H (Pi.single j 1) (Pi.single i 1) = H i j := by sorry
