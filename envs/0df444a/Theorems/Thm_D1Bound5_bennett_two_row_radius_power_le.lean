-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_row_radius_power_le
-- name    : D1Bound5.bennett_two_row_radius_power_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:49.889993+00:00
-- url     : https://prove2.me/theorems/ea86846d-6660-469b-8a16-ca73517fb6b8
-- title:
--   Bennett two row radius power le
-- statement:
--   The one extra pole in a residue row always pays for the coefficient radius. This is the algebraic counterpart of cancellation of circle length with the extra pole in the contour proof.
-- source:
--   D1Bound5/BennettTwoCoefficientConstants.lean, lines 17-49, SHA-256 034cf7aa6d3e853901a9f7bd5f2be74a2cd9af0c2f34f1de6a52a0f80541821b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5




theorem _root_.D1Bound5.bennett_two_row_radius_power_le
    (r D E : ℝ) (hr : 0 < r) (hD : r ≤ D) (hE : r ≤ E)
    (k d0 d1 d2 : ℕ) (hk : 1 ≤ k) (hd : d0 + d1 + d2 = 1) :
    (r * D * E) ^ k ≤ r ^ (k + d0 - 1) * D ^ (k + d1) * E ^ (k + d2) := by sorry







end D1Bound5
end
