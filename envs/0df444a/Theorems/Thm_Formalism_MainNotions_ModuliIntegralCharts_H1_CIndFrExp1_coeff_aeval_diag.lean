-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_coeff_aeval_diag
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.coeff_aeval_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:50:25.344834+00:00
-- url     : https://prove2.me/theorems/f13b0729-bc71-4db9-a91a-5e79e2d58163
-- title:
--   CInd Fr Exp1: coeff aeval diag
-- statement:
--   The CInd Fr Exp1 construction uses the coeff aeval diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L503-L515
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L503-L515

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.coeff_aeval_diag {σ : Type} (s : σ → S) (h : MvPolynomial σ S) (e : σ →₀ ℕ) :
    coeff e (aeval (fun p => C (s p) * X p) h) = (e.prod fun p k => s p ^ k) * coeff e h := by sorry
