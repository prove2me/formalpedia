-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_length_quot_map_of_injective
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_of_injective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:06.100796+00:00
-- url     : https://prove2.me/theorems/b0623d21-142a-429b-a15f-9a599982edb4
-- title:
--   Local Lattice Bases: length quot map of injective
-- statement:
--   The Local Lattice Bases construction uses the length quot map of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L102-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L102-L119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.length_quot_map_of_injective {O M M' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (hf : Function.Injective f) (A B : Submodule O M) :
    Module.length O (A.map f ⧸ (B.map f).comap (A.map f).subtype) = Module.length O (A ⧸ B.comap A.subtype) := by sorry
