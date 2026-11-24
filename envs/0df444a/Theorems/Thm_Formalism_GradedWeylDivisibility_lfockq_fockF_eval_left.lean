-- Prove2me | Theorems.Thm_Formalism_GradedWeylDivisibility_lfockq_fockF_eval_left
-- name    : Formalism.GradedWeylDivisibility.lfockq_fockF_eval_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:31.305949+00:00
-- url     : https://prove2.me/theorems/7d6ef251-ef3d-4d15-bcd0-367b85357498
-- title:
--   Graded Weyl Divisibility: lfockq fock F eval left
-- statement:
--   The Graded Weyl Divisibility construction uses the lfockq fock F eval left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GradedWeylDivisibility/FockSpaceTableaux/FockQRowDivAdj.lean#L76-L81

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility

theorem Formalism.GradedWeylDivisibility.lfockq_fockF_eval_left {σ : Type*} (P : Polynomial (MvPolynomial σ ℂ)) (N : ℕ)
    (hN : P.natDegree < N) (t : ℂ) (G : MvPolynomial σ ℂ) :
    fockF (Polynomial.eval (C t) P) G = ∑ i ∈ Finset.range N, t ^ i * fockF (P.coeff i) G := by sorry
