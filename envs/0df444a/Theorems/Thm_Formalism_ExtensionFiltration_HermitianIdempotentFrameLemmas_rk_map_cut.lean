-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_rk_map_cut
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_map_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:26.394856+00:00
-- url     : https://prove2.me/theorems/d2bf2e0f-28f1-4471-a349-5d045fdc6af7
-- title:
--   Hermitian Idempotent Frame Lemmas: rk map cut
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the rk map cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L279-L297
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L279-L297

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
variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rk_map_cut (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hg : 1 ≤ g)
    (hee : e ∘ₗ e = e) (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) =
      rkK (N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K))) := by sorry
