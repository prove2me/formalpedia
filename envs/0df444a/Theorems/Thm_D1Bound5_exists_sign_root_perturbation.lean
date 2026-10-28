-- Prove2me | Theorems.Thm_D1Bound5_exists_sign_root_perturbation
-- name    : D1Bound5.exists_sign_root_perturbation
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:03.189147+00:00
-- url     : https://prove2.me/theorems/3549d92c-d063-465e-bb4a-41d896fb435b
-- title:
--   Exists sign root perturbation
-- statement:
--   Choose the sign of a square root close to a prescribed nonzero target. The error estimate is multiplicative, with no division by the root.
-- source:
--   D1Bound5/RootPerturbation.lean, lines 35-66, SHA-256 7aaad87d1ed5a59f43b252455f1ebbb4d1f05aeee8eed1621908f38851f48649. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.exists_sign_root_perturbation (u t : ℂ) (c E : ℝ)
    (ht : t ≠ 0) (hc : 0 ≤ c) (hE : 0 < E)
    (herr : ‖u^2-t^2‖ ≤ E) (hgap : E < (1-c^2)*‖t‖^2) :
    ∃ v : ℂ, (v = u ∨ v = -u) ∧ (1+c)*‖t‖*‖v-t‖ < E := by sorry

end D1Bound5
end
