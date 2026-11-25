-- Prove2me | Theorems.Thm_Formalism_BranchingDeterminantCap_xnInv_pow
-- name    : Formalism.BranchingDeterminantCap.xnInv_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:00.881989+00:00
-- url     : https://prove2.me/theorems/d98726d5-708b-4bb1-97fa-14566cc82e79
-- title:
--   Branching Determinant Cap: xn Inv pow
-- statement:
--   The Branching Determinant Cap construction uses the xn Inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L818-L836
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean#L818-L836

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
variable {r n : ℕ}

theorem Formalism.BranchingDeterminantCap.xnInv_pow {k : ℕ} {μ : ℕ → ℕ} {x h : MvPolynomial (Fin r × Fin n) ℂ} (H : xnInv k μ x h)
    (hk : k ≤ n) (hkr : k ≤ r) (J : Fin k → Fin r) (hJ : Function.Injective J) (e : ℕ) :
    xnInv k (fun q => μ q + if q < k then e else 0) (initMinor ℂ J hk ^ e * x)
      (lpMinor ℂ k hkr hk ^ e * h) := by sorry
