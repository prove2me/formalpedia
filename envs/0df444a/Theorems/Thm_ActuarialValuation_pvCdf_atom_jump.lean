-- Prove2me | Theorems.Thm_ActuarialValuation_pvCdf_atom_jump
-- name    : ActuarialValuation.pvCdf_atom_jump
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:23:00.91045+00:00
-- url     : https://prove2.me/theorems/516618c5-39c1-4657-bb35-66c052597fd6
-- title:
--   Actual loss distribution and percentile premium adequacy: pvCdf_atom_jump
-- statement:
--   Exact-value atomic mass is included in the cumulative distribution at that boundary.
--
--   Mathematical relation:
--
--   $$
--   pvCdf\_atom\_jump
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvMass
import Definitions.Def_actuarial_pvCdf

namespace ActuarialValuation

theorem pvCdf_atom_jump {n : ℕ} (p loss : Fin n → ℝ) (z : ℝ) (hp : ∀ i, 0 ≤ p i) : pvMass p loss z ≤ pvCdf p loss z := by sorry

end ActuarialValuation
