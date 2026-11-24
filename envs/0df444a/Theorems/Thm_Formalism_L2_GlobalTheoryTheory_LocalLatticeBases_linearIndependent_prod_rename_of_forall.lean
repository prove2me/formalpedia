-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_prod_rename_of_forall
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_forall
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:34.526802+00:00
-- url     : https://prove2.me/theorems/8075eceb-5b7a-4374-8761-7c849c57e58b
-- title:
--   Local Lattice Bases: linear Independent prod rename of forall
-- statement:
--   The Local Lattice Bases construction uses the linear Independent prod rename of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L95-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L95-L98

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_forall {ι σ : Type} [Fintype ι] [DecidableEq ι] (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K)
    (hb : ∀ τ, LinearIndependent K (b τ)) :
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by sorry
