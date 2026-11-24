-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_bilin_of_biadd
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.bilin_of_biadd
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T09:57:37.110818+00:00
-- url     : https://prove2.me/theorems/92bf4895-febd-4f11-a9f8-9024e3a997c5
-- title:
--   CInd Fr Exp1: bilin of biadd
-- statement:
--   The CInd Fr Exp1 construction uses the bilin of biadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L536-L594
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L536-L594

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.bilin_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S}
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) :
    h = ∑ i, ∑ l, C (coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), l) 1) h) *
      (X ((0 : Fin 2), i) * X ((1 : Fin 2), l)) := by sorry
