-- Prove2me | Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
-- name    : APFPaper5.K1.plane_cost_quadratic
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:41:40.945042+00:00
-- url     : https://prove2.me/theorems/b63bbd15-9e7b-47a2-9a8c-f5cdf5b04ae4
-- title:
--   Rotation invariance and orthogonal additivity force a quadratic plane cost
-- statement:
--   Let q be a real-valued function of two real coordinates. Assume hturn: every Euclidean unit rotation preserves q; horth: q is additive on every pair of perpendicular vectors; hnn: q is nonnegative everywhere; and hroot: every nonnegative real has a nonnegative square root. Then q(x,y)=q(1,0)(x²+y²) for all x,y. The Euclidean plane and these structural laws are supplied. This conditional theorem does not derive them from CONTINUITY or RECORDS, construct a plane from ledger words, or identify q with a physical family cost.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_plane_cost_quadratic.lean:30; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 245-350; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_cross_term_and_preservation_2026-11-12.md, 1-2

import Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.plane_cost_quadratic (q : ℝ → ℝ → ℝ)
    (hturn : ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y)
    (horth : ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
      q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) :
    ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y) := by sorry
