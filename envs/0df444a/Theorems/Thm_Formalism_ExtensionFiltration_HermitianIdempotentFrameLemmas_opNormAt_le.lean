-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_opNormAt_le
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.opNormAt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:20.550232+00:00
-- url     : https://prove2.me/theorems/7b7938a7-a926-4e6c-83a1-d1a147b2c71e
-- title:
--   Hermitian Idempotent Frame Lemmas: op Norm At le
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the op Norm At le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L107-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L107-L143

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

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.opNormAt_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (g : ℕ) (v : InfinitePlace K) (hee : e ∘ₗ e = e)
    (hsa : ∀ x y, Formalism.HermitianLatticesTheory.majAt b X v (e x) y = Formalism.HermitianLatticesTheory.majAt b X v x (e y)) :
    opNormAt b X b X v ((g : K) • (LinearMap.id - e)) ≤ (g : ℝ) := by sorry
