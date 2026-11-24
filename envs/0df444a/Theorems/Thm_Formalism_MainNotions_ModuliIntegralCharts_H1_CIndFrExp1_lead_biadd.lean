-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_CIndFrExp1_lead_biadd
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.lead_biadd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:57.892193+00:00
-- url     : https://prove2.me/theorems/296fe2fe-e407-456b-987c-2f9370aec86c
-- title:
--   CInd Fr Exp1: lead biadd
-- statement:
--   The CInd Fr Exp1 construction uses the lead biadd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L166-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/AevalDiagMonomial.lean#L166-L263

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

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrExp1.lead_biadd {P : MvPolynomial (Fin 2 × Fin d) S} {m j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m)
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (hP : P - 1 ∈ Io S (Fin 2 × Fin d) ^ j) :
    ev2 (homogeneousComponent j (P - 1)) (fun i => xs S d (0 : Fin 3) i + xs S d 1 i) (xs S d 2) =
        ev2 (homogeneousComponent j (P - 1)) (xs S d 0) (xs S d 2) +
          ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 2) ∧
      ev2 (homogeneousComponent j (P - 1)) (xs S d 1) (xs S d 0) = homogeneousComponent j (P - 1) := by sorry
