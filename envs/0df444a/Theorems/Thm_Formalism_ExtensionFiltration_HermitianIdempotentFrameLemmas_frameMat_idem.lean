-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_frameMat_idem
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.frameMat_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:05.081288+00:00
-- url     : https://prove2.me/theorems/3d0dac11-4f3e-48a7-b895-414653352323
-- title:
--   Hermitian Idempotent Frame Lemmas: frame Mat idem
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the frame Mat idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L95-L105

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.frameMat_idem (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (v : InfinitePlace K) (hee : e ∘ₗ e = e) :
    ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) *
      ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) =
      (X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v := by sorry
