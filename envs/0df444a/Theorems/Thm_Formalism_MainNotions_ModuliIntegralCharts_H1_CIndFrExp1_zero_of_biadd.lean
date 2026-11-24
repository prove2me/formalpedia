-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_zero_of_biadd
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.zero_of_biadd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:57:27.704928+00:00
-- url     : https://prove2.me/theorems/dae4d3d5-a29c-49fa-b7c5-f6813b8ee98c
-- title:
--   CInd Fr Exp1: zero of biadd
-- statement:
--   The CInd Fr Exp1 construction uses the zero of biadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L386-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L386-L397

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.zero_of_biadd {h : MvPolynomial (Fin 2 × Fin d) S} {j : ℕ} (hh : h.IsHomogeneous j) (hj2 : j ≠ 2)
    (hA1 : ev2 h (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
      ev2 h (xs S d 0) (xs S d 2) + ev2 h (xs S d 1) (xs S d 2))
    (hs : ev2 h (xs S d 1) (xs S d 0) = h) : h = 0 := by sorry
