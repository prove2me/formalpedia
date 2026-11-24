-- Prove2me | Theorems.Thm_Formalism_L2_Pj_nval_smul
-- name    : Formalism.L2.Pj.nval_smul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:40.685299+00:00
-- url     : https://prove2.me/theorems/cda6fb16-e206-418a-9b72-ba88bb34da2e
-- title:
--   Pj: nval smul
-- statement:
--   The Pj construction uses the nval smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L130-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L130-L135

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
variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]
variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']

theorem Formalism.L2.Pj.nval_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (x : K') :
    nval V e (ι a * x) = (((vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by sorry
