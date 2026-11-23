-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nrmOf_smul
-- name    : Formalism.L2.Pj.nrmOf_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:14:56.305941+00:00
-- url     : https://prove2.me/theorems/feed5a63-2b06-495c-a5d0-6a5e541dba31
-- title:
--   Pj: nrm Of smul
-- statement:
--   The Pj construction uses the nrm Of smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L183-L191

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

theorem Formalism.L2.Pj.nrmOf_smul {a : K} (ha : a ≠ 0) {v : EReal} (hv : v ≠ ⊥) :
    nrmOf la ((((vLa la a : ℤ) : ℝ) : EReal) + v) = FinitePlace.mk la a * nrmOf la v := by sorry
