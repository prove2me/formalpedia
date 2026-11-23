-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xn_stage
-- name    : Formalism.BranchingDeterminantCap.xn_stage
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:32.837728+00:00
-- url     : https://prove2.me/theorems/6f23b9da-e8f8-4c69-9d1e-31fdc7f151c0
-- title:
--   Branching Determinant Cap: xn stage
-- statement:
--   The Branching Determinant Cap construction uses the xn stage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L892-L941
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L892-L941

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

theorem Formalism.BranchingDeterminantCap.xn_stage (n : ℕ) (lam sg : Fin n → ℕ) (hI : Interlace (lamZ lam) (fun i => (sg i : ℤ)))
    (k : ℕ) (hk : k ≤ n) :
    xnInv (r := n + 1) (n := n) k (fun q => xnLam lam q - xnLam lam k)
      (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k),
        (initMinor ℂ (rowsA i) (by omega : i.val + 1 ≤ n) ^ (sg i - nuNext lam i) *
          initMinor ℂ (rowsB i) (by omega : i.val + 1 ≤ n) ^ (lam i - sg i)))
      (∏ s ∈ Finset.univ.filter (fun s : Fin n => s.val < k),
        (lpMinor ℂ (s.val + 1) (by omega) (by omega)) ^ (lam s - nuNext lam s)) := by sorry
