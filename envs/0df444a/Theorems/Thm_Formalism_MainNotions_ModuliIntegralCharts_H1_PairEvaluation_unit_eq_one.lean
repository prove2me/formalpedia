-- Prove2me | Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_PairEvaluation_unit_eq_one
-- name    : Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.unit_eq_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:45.344849+00:00
-- url     : https://prove2.me/theorems/0b2c6481-c472-4745-aa9a-f262272b8ff7
-- title:
--   Pair Evaluation: unit eq one
-- statement:
--   The Pair Evaluation construction uses the unit eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L404-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/PairEvaluation.lean#L404-L448

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_PairEvaluation
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
open Formalism Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation
open MvPolynomial
variable {S : Type} [CommRing S] {d : ℕ}
variable [Algebra ℚ S]

theorem Formalism.MainNotions.ModuliIntegralCharts.H1.PairEvaluation.unit_eq_one {P : MvPolynomial (Fin 2 × Fin d) S} {m : ℕ}
    (fF : Fin d → MvPolynomial (Fin 3 × Fin d) S)
    (hF : ∀ i, fF i - (xs S d 0 i + xs S d 1 i) ∈ Io S (Fin 3 × Fin d) ^ 2)
    (hph1 : ev2 P fF (xs S d 2) - ev2 P (xs S d 0) (xs S d 2) * ev2 P (xs S d 1) (xs S d 2) ∈
      Io S (Fin 3 × Fin d) ^ (m + 1))
    (hsym : ev2 P (xs S d 1) (xs S d 0) - P ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (A Ab : Fin d → Fin d → S) (hAA : ∀ i l, A i l + Ab i l = if i = l then 1 else 0)
    (aW0 aB1 : Fin d → MvPolynomial (Fin 2 × Fin d) S)
    (hW0 : ∀ i, aW0 i - lin A 0 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hB1 : ∀ i, aB1 i - lin Ab 1 i ∈ Io S (Fin 2 × Fin d) ^ 2)
    (hbal : ev2 P aW0 (xs S d 1) - ev2 P (xs S d 0) aB1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1))
    (aW : Fin d → MvPolynomial (Fin 1 × Fin d) S) (hW : ∀ i, aW i - lin A 0 i ∈ Io S (Fin 1 × Fin d) ^ 2)
    (hdiag : ev2 P (xs S d 0) aW - 1 ∈ Io S (Fin 1 × Fin d) ^ (m + 1)) :
    P - 1 ∈ Io S (Fin 2 × Fin d) ^ (m + 1) := by sorry
