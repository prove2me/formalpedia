-- Prove2me | Theorems.Thm_Formalism_L2_Pj_one_lt_absNorm_real
-- name    : Formalism.L2.Pj.one_lt_absNorm_real
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:48.353805+00:00
-- url     : https://prove2.me/theorems/50ec435b-2178-458a-bc93-fc7cfb400b44
-- title:
--   Pj: one lt abs Norm real
-- statement:
--   The Pj construction uses the one lt abs Norm real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L171-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L171-L172

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped WithZero
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

theorem Formalism.L2.Pj.one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by sorry
