-- Prove2me | Theorems.Thm_APFPaper5_K1_plane_K1_of_clauses
-- name    : APFPaper5.K1.plane_K1_of_clauses
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:52:14.730196+00:00
-- url     : https://prove2.me/theorems/10d038e1-8cf2-4dbd-90d2-7c2a9fbdbc5b
-- title:
--   Explicit plane cost laws give a bilinear cross form with faithful diagonal
-- statement:
--   Let q be a real-valued plane cost. Assume hturn: invariance under every Euclidean unit rotation; horth: additivity for all perpendicular pairs; hnn: global nonnegativity; hroot: every nonnegative real has a nonnegative square root; and hc: q(1,0)>0. Then crossForm(q), half its additive cost excess, is real-bilinear and has a faithful nonnegative diagonal with identity role exchange. This supplies the displayed algebraic predicates on the given plane. It does not discharge physical K1 or derive the supplied geometric laws from the foundation.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_plane_K1.lean:67; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 245-391;3038-3041

import Definitions.Def_APFPaper5_K1_CrossForm
import Definitions.Def_APFPaper5_K1_OrderedScore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.plane_K1_of_clauses (q : ℝ → ℝ → ℝ)
    (hturn : ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y)
    (horth : ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
      q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (hc : 0 < q 1 0) :
    IsBilinear (VP := Bool → ℝ) (VE := Bool → ℝ) (crossForm q) ∧
      FaithfulNonnegDiagonal (crossForm q) (LinearEquiv.refl ℝ (Bool → ℝ)) := by sorry
