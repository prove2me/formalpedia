-- Prove2me | Theorems.Thm_Formalism_G_LogP_subst2_subst
-- name    : Formalism.G.LogP.subst2_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:44.495525+00:00
-- url     : https://prove2.me/theorems/076afa3f-88d0-4163-bcfa-ed38cc810578
-- title:
--   Log P: subst2 subst
-- statement:
--   The Log P construction uses the subst2 subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupLog/FormalGroupLogProofs/ConstantCoeffSubstOfZero.lean#L22-L29

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

theorem Formalism.G.LogP.subst2_subst {σ τ : Type*} (Φ : MvPowerSeries (Fin 2) R) {u v : MvPowerSeries σ R}
    (hu : constantCoeff u = 0) (hv : constantCoeff v = 0) {b : σ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) :
    (Φ.subst ![u, v]).subst b = Φ.subst ![u.subst b, v.subst b] := by sorry
