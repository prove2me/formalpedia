-- Prove2me | Theorems.Thm_Formalism_L2_NCov_chi_add
-- name    : Formalism.L2.NCov.chi_add
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:14.557856+00:00
-- url     : https://prove2.me/theorems/f6458995-fc8f-433d-9df9-948cb3214c4d
-- title:
--   NCov: chi add
-- statement:
--   The NCov construction uses the chi add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L133-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/CoverAlg.lean#L133-L136

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

theorem Formalism.L2.NCov.chi_add (hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b) {χ : Algebra.adjoin O S → K}
    (hW : W _ χ ≠ ⊥) (s t : Algebra.adjoin O S) : χ (s + t) = χ s + χ t := by sorry
