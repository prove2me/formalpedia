-- Prove2me | Theorems.Thm_Formalism_L2_NCov_chi_int
-- name    : Formalism.L2.NCov.chi_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:34.705918+00:00
-- url     : https://prove2.me/theorems/f50be6ec-85dc-4771-afe9-82c9aabcfdb2
-- title:
--   NCov: chi int
-- statement:
--   The NCov construction uses the chi int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L149-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L149-L165

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

theorem Formalism.L2.NCov.chi_int (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b)
    (hint : ∀ a ∈ S, ∀ μ, a.maxGenEigenspace μ ≠ ⊥ → μ ∈ (algebraMap O K).range)
    {χ : Algebra.adjoin O S → K} (hW : W _ χ ≠ ⊥) (t : Algebra.adjoin O S) :
    χ t ∈ (algebraMap O K).range := by sorry
