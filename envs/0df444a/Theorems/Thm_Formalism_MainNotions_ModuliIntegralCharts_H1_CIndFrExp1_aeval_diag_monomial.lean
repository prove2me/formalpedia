-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_aeval_diag_monomial
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.aeval_diag_monomial
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:26.083813+00:00
-- url     : https://prove2.me/theorems/660d7132-2f8a-4645-a199-8632cfeaf59f
-- title:
--   CInd Fr Exp1: aeval diag monomial
-- statement:
--   The CInd Fr Exp1 construction uses the aeval diag monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L497-L501
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L497-L501

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_AevalDiagMonomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1
open MvPolynomial Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.aeval_diag_monomial {σ : Type} (s : σ → S) (e : σ →₀ ℕ) (a : S) :
    aeval (fun p => C (s p) * X p) (monomial e a) = monomial e ((e.prod fun p k => s p ^ k) * a) := by sorry
