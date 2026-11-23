-- Prove2me | Theorems.Thm_Formalism_L2_Pj_OverLa_bc
-- name    : Formalism.L2.Pj.OverLa.bc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:06:01.873184+00:00
-- url     : https://prove2.me/theorems/08d04beb-227a-4f1e-b390-3c4c7229a835
-- title:
--   Over La: bc
-- statement:
--   The Over La construction uses the bc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L137-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L137-L141

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

theorem Formalism.L2.Pj.OverLa.bc {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {V' K'' : Type} [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K''] [IsFractionRing V' K'']
    (i : K' →+* K'') {r : ℕ} (hr : 0 < r) (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) :
    OverLa la V' (i.comp ι) (r * e) := by sorry
