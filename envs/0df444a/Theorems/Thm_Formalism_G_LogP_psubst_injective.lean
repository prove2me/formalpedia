-- Prove2me | Theorems.Thm_Formalism_G_LogP_psubst_injective
-- name    : Formalism.G.LogP.psubst_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:59.213724+00:00
-- url     : https://prove2.me/theorems/2c59fa26-f242-42c7-949e-2fe0f0fc1fda
-- title:
--   Log P: psubst injective
-- statement:
--   The Log P construction uses the psubst injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L319-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L319-L329

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
variable {R : Type*} [CommRing R]

theorem Formalism.G.LogP.psubst_injective {f : PowerSeries R} (hf0 : PowerSeries.constantCoeff f = 0)
    (hf1 : PowerSeries.coeff 1 f = 1) {σ : Type*} {a b : MvPowerSeries σ R}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) (h : f.subst a = f.subst b) : a = b := by sorry
