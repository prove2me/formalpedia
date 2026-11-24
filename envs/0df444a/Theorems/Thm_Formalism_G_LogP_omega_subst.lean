-- Prove2me | Theorems.Thm_Formalism_G_LogP_omega_subst
-- name    : Formalism.G.LogP.omega_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:30.384382+00:00
-- url     : https://prove2.me/theorems/28e3e86c-99bd-432e-a2a5-89a163aa9348
-- title:
--   Log P: omega subst
-- statement:
--   The Log P construction uses the omega subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L151-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L151-L163

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
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]

theorem Formalism.G.LogP.omega_subst {σ : Type*} {u : MvPowerSeries σ R} (hu : constantCoeff u = 0)
    (F : FormalGroup R) :
    (omegaF F).subst u = (MvPowerSeries.pderiv R 1 F.toPowerSeries).subst ![u, 0] := by sorry
