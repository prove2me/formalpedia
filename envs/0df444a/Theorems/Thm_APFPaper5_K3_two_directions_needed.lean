-- Prove2me | Theorems.Thm_APFPaper5_K3_two_directions_needed
-- name    : APFPaper5.K3.two_directions_needed
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:46:31.417458+00:00
-- url     : https://prove2.me/theorems/bb9d740c-80bf-490a-824b-599d986af820
-- title:
--   Two directions needed
-- statement:
--   For a symmetric bilinear form preserved by T, if the square of B(z,Tz) differs from the square of B(z,z), the vectors z and Tz are linearly independent. FirstOrder means second iterate in a two-vector span, not equivalence to faithful differentiable first jets or a derivation from economy. The reverse implication and exact two-dimensional physical minimality are not certified.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650,2058-2090'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_firstOrder_economy.lean', 'sha256': '18c13508d187b79c5c4e62912fc2007b8a37738e601401e754d9db7bbe19fd59', 'line': 45, 'declaration': 'APFPaper5.K3.two_directions_needed'}]

import Definitions.Def_APFPaper5_K3_FirstOrder
import Definitions.Def_APFPaper5_K1_OrderedScore
import Definitions.Def_APFPaper5_K4_TwoSheets
import Theorems.Thm_APFPaper5_K3_records_of_plainAfterTurn_eq
import Theorems.Thm_APFPaper5_K3_plainAfterTurn_eq_iff_records
import Theorems.Thm_APFPaper5_K3_pair_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_dichotomy
import Theorems.Thm_APFPaper5_K3_unseen_of_anticommutes
import Theorems.Thm_APFPaper5_K3_unseen_iff
import Theorems.Thm_APFPaper5_K3_square_commutes_quarter
import Theorems.Thm_APFPaper5_K3_unseen_of_fixed_by_records
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
open APFPaper5.K1

theorem APFPaper5.K3.two_directions_needed {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V → V → ℝ)
    (hB : IsBilinear B) (hsym : ∀ x y : V, B x y = B y x) (T : V → V)
    (hT : ∀ x y : V, B (T x) (T y) = B x y) (z : V)
    (hne : B z (T z) * B z (T z) ≠ B z z * B z z) :
    ∀ a b : ℝ, a • z + b • T z = 0 → a = 0 ∧ b = 0 := by sorry
