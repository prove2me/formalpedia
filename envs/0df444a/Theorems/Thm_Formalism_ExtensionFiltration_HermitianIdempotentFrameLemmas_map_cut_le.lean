-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_map_cut_le
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.map_cut_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:26.412709+00:00
-- url     : https://prove2.me/theorems/a3c0ad93-dbc4-418c-918d-11e22d09cda7
-- title:
--   Hermitian Idempotent Frame Lemmas: map cut le
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the map cut le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L263-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L263-L268

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

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.map_cut_le (e : V →ₗ[K] V) (g : ℕ) (N : Submodule (𝓞 K) V) (hee : e ∘ₗ e = e)
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) :
    N.map (((g : K) • (LinearMap.id - e) : V →ₗ[K] V).restrictScalars (𝓞 K)) ≤
      N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K) := by sorry
