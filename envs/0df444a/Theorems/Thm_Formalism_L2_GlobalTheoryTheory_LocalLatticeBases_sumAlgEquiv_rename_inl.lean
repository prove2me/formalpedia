-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inl
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.sumAlgEquiv_rename_inl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:14:06.581064+00:00
-- url     : https://prove2.me/theorems/506f031c-211b-47dd-ae12-324c8e6c2516
-- title:
--   Local Lattice Bases: sum Alg Equiv rename inl
-- statement:
--   The Local Lattice Bases construction uses the sum Alg Equiv rename inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L11-L14

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.sumAlgEquiv_rename_inl (a : MvPolynomial S₁ K) :
    sumAlgEquiv K S₁ S₂ (rename Sum.inl a) = map (C : K →+* MvPolynomial S₂ K) a := by sorry
