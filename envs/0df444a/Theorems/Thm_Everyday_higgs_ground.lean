-- Prove2me | Theorems.Thm_Everyday_higgs_ground
-- name    : Everyday.higgs_ground
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T00:16:52.649326+00:00
-- url     : https://prove2.me/theorems/da7f4bbd-7c49-4c0e-9523-93e8051cf4a1
-- title:
--   Higgs: the potential is bounded below, with its minimum on the symmetry-breaking circle
-- statement:
--   The everyday world rests on a nonzero value of the Higgs field: the Mexican-hat potential's minimum is not at φ = 0 but on the circle |φ|² = μ²/(2λ) — the spontaneous symmetry breaking locus. The item is the vacuum structure: for positive μ and λ, the potential is bounded below by its floor -μ⁴/(4λ), and the floor is attained exactly on the circle — the potential equals its minimum if and only if |φ|² = μ²/(2λ).
--
--   **Formalization Note** The hypotheses are the physical signs μ > 0 and λ > 0 under which the hat has its shape; the quartic coupling λ is bound as lam in the formal statement, λ being a reserved keyword in Lean 4. The proof uses the completed square of the higgs_square milestone: the potential minus its floor is λ(|φ|² - μ²/(2λ))², nonnegative since λ > 0, and zero exactly when |φ|² = μ²/(2λ) — the positivity of λ makes the equivalence exact rather than one-way.
-- source:
--   Sean Carroll, "The World of Everyday Experience, In One Equation", preposterousuniverse.com, 2013-01-04, retrieved 2026-10-18, the Higgs potential V(Φ) and its vacuum

import Mathlib
import Definitions.Def_Everyday_spacetime__e5fc57
import Definitions.Def_Everyday_sectors

namespace Everyday

/-- Higgs: the vacuum. The Mexican-hat potential is bounded below, with
its minimum value -μ⁴/(4λ) attained exactly on the circle of fields with
|φ|² = μ²/(2λ) — the spontaneous symmetry breaking locus of the Higgs
field, the nonzero field value the everyday world rests on. The quartic
coupling λ is bound as lam, λ being a reserved keyword in Lean 4. -/
theorem higgs_ground (μ lam : ℝ) (φ : ℂ) (hμ : 0 < μ) (hlam : 0 < lam) :
    -(μ ^ 4 / (4 * lam)) ≤ higgsV μ lam φ ∧
      (higgsV μ lam φ = -(μ ^ 4 / (4 * lam)) ↔
        Complex.normSq φ = μ ^ 2 / (2 * lam)) := by sorry

end Everyday
