-- Prove2me | Theorems.Thm_D1Bound5_bennett_prefactor_absorb
-- name    : D1Bound5.bennett_prefactor_absorb
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:23.657297+00:00
-- url     : https://prove2.me/theorems/6187e44e-3f5a-4024-9f7b-ad39a7c28893
-- title:
--   Bennett prefactor absorb
-- statement:
--   A prefactor at least one can be absorbed into an exponential at every positive order, allowing the preceding exact rational slack to be used.
-- source:
--   D1Bound5/BennettTwoCoefficientConstants.lean, lines 101-118, SHA-256 034cf7aa6d3e853901a9f7bd5f2be74a2cd9af0c2f34f1de6a52a0f80541821b. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5










theorem _root_.D1Bound5.bennett_prefactor_absorb (M H : ℝ) (hM : 1 ≤ M) (hH : 0 ≤ H)
    (k : ℕ) (hk : 1 ≤ k) : M * H ^ k ≤ (M * H) ^ k := by sorry

end D1Bound5
end
