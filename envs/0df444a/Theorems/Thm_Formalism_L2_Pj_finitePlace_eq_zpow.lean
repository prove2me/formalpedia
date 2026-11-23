-- Prove2me | Theorems.Thm_Formalism_L2_Pj_finitePlace_eq_zpow
-- name    : Formalism.L2.Pj.finitePlace_eq_zpow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:20.915728+00:00
-- url     : https://prove2.me/theorems/90f35b0b-4274-406b-8993-c54a9e815080
-- title:
--   Pj: finite Place eq zpow
-- statement:
--   The Pj construction uses the finite Place eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L162-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L162-L166

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

theorem Formalism.L2.Pj.finitePlace_eq_zpow {a : K} (ha : a ≠ 0) :
    FinitePlace.mk la a = (Ideal.absNorm la.asIdeal : ℝ) ^ (-(vLa la a)) := by sorry
