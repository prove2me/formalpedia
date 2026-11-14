-- Prove2me | Theorems.Thm_APFPaper5_K1_square_of_cross_term
-- name    : APFPaper5.K1.square_of_cross_term
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:46:27.759451+00:00
-- url     : https://prove2.me/theorems/18a67ae5-694f-4ef4-b132-d7ee6ef5300f
-- title:
--   The squared normalized quadratic cost excess equals the squared first coordinate
-- statement:
--   Let q satisfy hq: q(x,y)=q(1,0)(x²+y²), and assume hc: q(1,0)≠0. For arbitrary real u,v, write E=q(1+u,v)−q(1,0)−q(u,v). Then (E/(2q(1,0)))²=u². This is an identity on a supplied quadratic plane cost. No unit-length condition on (u,v) is included. Identifying the squared expression with a two-mark pair number requires the separate model and normalization correspondence; this declaration alone establishes no physical probability rule.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_plane_cost_quadratic.lean:90; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 245-350; Artifacts_2026-11-12_session/claude/EthanBrooke-01WrrBvu/RULING_cross_term_and_preservation_2026-11-12.md, 1-2

import Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1

theorem APFPaper5.K1.square_of_cross_term (q : ℝ → ℝ → ℝ)
    (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y)) (hc : q 1 0 ≠ 0) (u v : ℝ) :
    (q (1 + u) (0 + v) - q 1 0 - q u v) / (2 * q 1 0) *
      ((q (1 + u) (0 + v) - q 1 0 - q u v) / (2 * q 1 0)) = u * u := by sorry
