-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_factorMap_injective
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.factorMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:08.919875+00:00
-- url     : https://prove2.me/theorems/7902f2d1-671a-4b4b-97c8-7fb7840f40bb
-- title:
--   Local Lattice Bases: factor Map injective
-- statement:
--   The Local Lattice Bases construction uses the factor Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L178-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L178-L194

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
variable {K : Type*} [Field K]

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.factorMap_injective {ι σ : Type} [Fintype ι] [DecidableEq ι] (τ₀ : ι) (κ : ι → Type) [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, κ τ → MvPolynomial σ K) (hb : ∀ τ, τ ≠ τ₀ → LinearIndependent K (b τ)) :
    Function.Injective (mvPolynomialProductExtension τ₀ κ b) := by sorry
