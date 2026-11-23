-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_U
-- name    : Formalism.BranchingDeterminantCap.xn_U
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:04.573621+00:00
-- url     : https://prove2.me/theorems/d5f1bdc5-20f7-4cd6-b94c-4f78f9089b4b
-- title:
--   Branching Determinant Cap: xn U
-- statement:
--   The Branching Determinant Cap construction uses the xn U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L467-L479
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L467-L479

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]

theorem Formalism.BranchingDeterminantCap.xn_U (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (J : Fin p → κ) (hJ : Function.Injective J) :
    xnN (initMinor ℂ (ι ∘ J) hp * f) ≤ xnC (Fintype.card κ) m p * xnN f := by sorry
