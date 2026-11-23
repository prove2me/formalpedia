-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_fock_pairing_initial_minor
-- name    : Formalism.BranchingDeterminantCap.fock_pairing_initial_minor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:28:24.471391+00:00
-- url     : https://prove2.me/theorems/f5ef7084-8e7c-4f84-941f-913f35e117a5
-- title:
--   Branching Determinant Cap: fock pairing initial minor
-- statement:
--   The Branching Determinant Cap construction uses the fock pairing initial minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L290-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L290-L338

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

theorem Formalism.BranchingDeterminantCap.fock_pairing_initial_minor (ι : κ → Fin r) (hι : Function.Injective ι) (m : ℕ → ℕ)
    (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hR : ∀ t s : Fin n, t < s → ∑ b : κ, X (ι b, t) * pderiv (ι b, s) f = 0)
    (hW : ∀ s : Fin n, ∑ b : κ, X (ι b, s) * pderiv (ι b, s) f = C ((m s.val : ℕ) : ℂ) * f)
    (p : ℕ) (hp : p ≤ n) (g : MvPolynomial (Fin r × Fin n) ℂ) :
    ∑ a : Fin p → κ, fockF (xnMono ι hp a * g) (initMinor ℂ (ι ∘ a) hp * f) =
      ((xnC (Fintype.card κ) m p : ℝ) : ℂ) * fockF g f := by sorry
