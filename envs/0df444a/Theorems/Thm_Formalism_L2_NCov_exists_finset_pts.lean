-- Prove2me | Theorems.Thm_Formalism_L2_NCov_exists_finset_pts
-- name    : Formalism.L2.NCov.exists_finset_pts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:58:50.141437+00:00
-- url     : https://prove2.me/theorems/31139461-6575-406d-afde-05ece5d18f0a
-- title:
--   NCov: exists finset pts
-- statement:
--   The NCov construction uses the exists finset pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L217-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L217-L231

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftLast_Pz
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoverAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.NCov
open Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
variable [IsLocalRing O]
variable {S : Set (End K V)}

theorem Formalism.L2.NCov.exists_finset_pts [FiniteDimensional K V] (hinj : Function.Injective (algebraMap O K))
    (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) (hsplit : ∀ a ∈ S, ⨆ μ, a.maxGenEigenspace μ = ⊤)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range) :
    ∃ F : Finset (Algebra.adjoin O S →ₐ[O] O),
      (∀ ψ, W _ (pt ψ) ≠ ⊥ → ψ ∈ F) ∧ F.sup (fun ψ => W _ (pt ψ)) = ⊤ := by sorry
