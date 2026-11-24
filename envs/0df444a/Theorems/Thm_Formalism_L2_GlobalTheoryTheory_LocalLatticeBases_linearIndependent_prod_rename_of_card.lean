-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_prod_rename_of_card
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:15.064949+00:00
-- url     : https://prove2.me/theorems/3a864591-6346-4af9-9951-72a914110c00
-- title:
--   Local Lattice Bases: linear Independent prod rename of card
-- statement:
--   The Local Lattice Bases construction uses the linear Independent prod rename of card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L58-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L58-L93

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_prod_rename_of_card (n : ℕ) : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n →
    ∀ {σ : Type} (κ : ι → Type) (b : ∀ τ, κ τ → MvPolynomial σ K), (∀ τ, LinearIndependent K (b τ)) →
    LinearIndependent K (fun g : (∀ τ, κ τ) => ∏ τ, rename (Prod.mk τ) (b τ (g τ))) := by sorry
