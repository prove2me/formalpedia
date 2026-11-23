-- Prove2me | Theorems.Thm_Formalism_ExtensionFiltration_HermitianIdempotentFrameLemmas_ker_cut
-- name    : Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.ker_cut
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:18.712643+00:00
-- url     : https://prove2.me/theorems/1ec290ca-e3e2-408d-b420-b776464a48e4
-- title:
--   Hermitian Idempotent Frame Lemmas: ker cut
-- statement:
--   The Hermitian Idempotent Frame Lemmas construction uses the ker cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L250-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MeanHeightDescent/AverageDegreeBounds/GoodBadCut.lean#L250-L261

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

theorem Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.ker_cut (e : V →ₗ[K] V) (g : ℕ) (hg : 1 ≤ g) (hee : e ∘ₗ e = e) :
    LinearMap.ker ((g : K) • (LinearMap.id - e)) = LinearMap.range e := by sorry
