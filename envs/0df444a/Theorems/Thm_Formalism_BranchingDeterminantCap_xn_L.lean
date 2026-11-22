-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_L
-- name    : Formalism.BranchingDeterminantCap.xn_L
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:23.228742+00:00
-- url     : https://prove2.me/theorems/14a173a7-3943-4255-892e-00faff0c46de
-- title:
--   Branching Determinant Cap: xn L
-- statement:
--   The Branching Determinant Cap construction uses the xn L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L481-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L481-L503

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

theorem Formalism.BranchingDeterminantCap.xn_L {p : ℕ} (ι : Fin p → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : Fin p, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : Fin p, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (hp : p ≤ n) :
    xnN (initMinor ℂ ι hp * f) = xnC p m p * xnN f := by sorry
