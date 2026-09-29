-- Prove2me | Theorems.Thm_BrinSquier_commute_of_disjoint_supp
-- name    : BrinSquier.commute_of_disjoint_supp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-12T22:05:51.475468+00:00
-- url     : https://prove2.me/theorems/3bf860b4-b9ee-4872-90f1-a50c2ad16a55
-- title:
--   Homeomorphisms with disjoint supports commute
-- statement:
--   If two orientation-preserving homeomorphisms of $\mathbb{R}$ move disjoint sets of points, they commute:
--
--   $$\operatorname{supp} f \cap \operatorname{supp} g = \varnothing \implies fg = gf.$$
--
--   Each map fixes everything the other moves, so the two actions never interfere.  No piecewise-linear hypothesis is required.
--
--   This is what makes disjointly supported elements generate an abelian group, and it is the commutation input to Lemma (1.2).
-- source:
--   M. G. Brin and C. C. Squier, Groups of piecewise linear homeomorphisms of the real line, Invent. math. 79 (1985), 485-498, https://doi.org/10.1007/BF01388519, p. 487, observation (1.1b).

import Definitions.Def_BrinSquier
import Mathlib

namespace BrinSquier

theorem commute_of_disjoint_supp {f g : ℝ ≃o ℝ} (h : Disjoint (supp f) (supp g)) :
    f * g = g * f := by
  sorry

end BrinSquier
