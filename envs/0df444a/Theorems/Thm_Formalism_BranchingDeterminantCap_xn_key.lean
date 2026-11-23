-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_key
-- name    : Formalism.BranchingDeterminantCap.xn_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:13.563687+00:00
-- url     : https://prove2.me/theorems/2e9cd0ec-8377-4336-909d-8ef0db093b02
-- title:
--   Branching Determinant Cap: xn key
-- statement:
--   The Branching Determinant Cap construction uses the xn key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L129-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L129-L161

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

theorem Formalism.BranchingDeterminantCap.xn_key (ι : κ → Fin r) (hι : Function.Injective ι) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (m : ℂ)
    (h0 : ∀ t : Fin n, t.val < p → ∑ b : κ, X (ι b, t) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = 0)
    (h1 : ∑ b : κ, X (ι b, (⟨p, hp⟩ : Fin n)) * pderiv (ι b, (⟨p, hp⟩ : Fin n)) f = C m * f) :
    ∑ b : κ, pderiv (ι b, (⟨p, hp⟩ : Fin n))
        (initMinor ℂ (ι ∘ (Fin.snoc a b : Fin (p + 1) → κ)) hp * f) =
      C ((Fintype.card κ : ℂ) - p + m) * (initMinor ℂ (ι ∘ a) (Nat.le_of_succ_le hp) * f) := by sorry
