-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_eq_zero_of_sum_rename_mul
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.eq_zero_of_sum_rename_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:08.276211+00:00
-- url     : https://prove2.me/theorems/3b697c0c-2dd1-430f-a7f4-0b3fd78634f4
-- title:
--   Local Lattice Bases: eq zero of sum rename mul
-- statement:
--   The Local Lattice Bases construction uses the eq zero of sum rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L163-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L163-L169

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.eq_zero_of_sum_rename_mul {S₁ S₂ κ : Type*} [Fintype κ] (w : κ → MvPolynomial S₂ K) (hw : LinearIndependent K w)
    (a : κ → MvPolynomial S₁ K) (h : ∑ j, rename Sum.inl (a j) * rename Sum.inr (w j) = 0) : a = 0 := by sorry
