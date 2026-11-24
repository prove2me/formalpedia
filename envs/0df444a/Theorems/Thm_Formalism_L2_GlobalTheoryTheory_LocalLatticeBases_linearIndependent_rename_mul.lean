-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_linearIndependent_rename_mul
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_rename_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:15.061105+00:00
-- url     : https://prove2.me/theorems/2edaca48-d9ca-4cc9-8c9f-119406ba6d3e
-- title:
--   Local Lattice Bases: linear Independent rename mul
-- statement:
--   The Local Lattice Bases construction uses the linear Independent rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L30-L44

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.linearIndependent_rename_mul {κ₁ κ₂ : Type*} (v : κ₁ → MvPolynomial S₁ K) (w : κ₂ → MvPolynomial S₂ K)
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K fun p : κ₁ × κ₂ => rename Sum.inl (v p.1) * rename Sum.inr (w p.2) := by sorry
