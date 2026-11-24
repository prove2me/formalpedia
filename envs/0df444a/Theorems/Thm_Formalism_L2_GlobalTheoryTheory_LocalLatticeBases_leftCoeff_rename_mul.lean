-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_leftCoeff_rename_mul
-- name    : Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.leftCoeff_rename_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:10.008194+00:00
-- url     : https://prove2.me/theorems/0a8aa090-bb1e-4aaf-ab01-1ef4f252b6a7
-- title:
--   Local Lattice Bases: left Coeff rename mul
-- statement:
--   The Local Lattice Bases construction uses the left Coeff rename mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L24-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL6/LinearIndependentProdRenameOfCard.lean#L24-L28

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

theorem Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.leftCoeff_rename_mul (m : S₁ →₀ ℕ) (a : MvPolynomial S₁ K) (b : MvPolynomial S₂ K) :
    mvPolynomialCoeffInFirstVariables m (rename Sum.inl a * rename Sum.inr b) = coeff m a • b := by sorry
