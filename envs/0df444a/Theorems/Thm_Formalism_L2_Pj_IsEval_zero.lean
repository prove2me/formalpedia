-- Prove2me | Theorems.Thm_Formalism_L2_Pj_IsEval_zero
-- name    : Formalism.L2.Pj.IsEval.zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:58.120797+00:00
-- url     : https://prove2.me/theorems/ecbf5df2-9618-4741-be10-86e2379ab0a5
-- title:
--   Is Eval: zero
-- statement:
--   The Is Eval construction uses the zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/OneLtAbsNormReal.lean#L150-L154

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

theorem Formalism.L2.Pj.IsEval.zero {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    {wadd : W → W → W} {mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')} {F : Type} [Field F]
    {ι : K →+* F} {ev : ∀ w, Cusp w → F} (h : IsEval wadd mulC ι ev) (w : W) : ev w 0 = 0 := by sorry
