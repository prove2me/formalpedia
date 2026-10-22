-- Prove2me | Theorems.Thm_CondC_disc_liquid
-- name    : CondC.disc_liquid
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-21T15:49:31.199068+00:00
-- url     : https://prove2.me/theorems/5eae5f83-1a86-4686-8c9c-bab74388eb2a
-- title:
--   The disc algebra is p-liquid (Lectures I-IV)
-- statement:
--   The first milestone of the mission: the liquidness of the disc algebra, the key hard theorem of the paper's liquid theory, on the way to the structure sheaf theorem. The paper proves that for each 0 < p at most 1, the space O(D) of holomorphic functions on an open disc is p-liquid; from this, Theorem 1.1's identification of O(D) with convergent power series and the tensor calculus of Theorem 4.1 both flow. The theorem states: for 0 < p at most 1 and 0 < r, any complex vector space carrying the disc algebra data of radius r - a bijective, linear identification with the power-series coefficients satisfying the decay condition of Theorem 1.1 - is p-liquid.
--
--   **Formalization Note** p-liquidness is recorded through the interface PLiquidStructure: the designated summable families, the designated null sequences, and the unique integration functional. Profinite sets are idealized as the one-point compactification of the naturals, and the null sequences are designated abstractly, as in the paper's first formulation of liquidness: every null sequence has a unique sum.
-- source:
--   D. Clausen, P. Scholze, Condensed Mathematics and Complex Geometry, lecture notes (May 2026 version), Lectures I-IV (the liquidness of O(D), toward Theorems 1.1, 4.1, and 5.1).

import Mathlib
import Definitions.Def_CondC_liq
import Definitions.Def_CondC_geo

namespace CondC

/-!  Milestone 1: the disc algebra is p-liquid. Any complex vector space
carrying the disc algebra data of radius r - elements identified
bijectively and linearly with the power series whose coefficients decay on
the disc of radius r - is p-liquid for every 0 < p at most 1. This is the
liquidness of O(D) on the way to Theorems 1.1 and 5.1.  -/
theorem disc_liquid : ∀ (p r : ℝ), 0 < p → p ≤ 1 → 0 < r →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V],
      DiscAlgebraData r V → IsPLiquid p V := by sorry

end CondC
