-- Prove2me | Theorems.Thm_FastCLO_LowerBound_rho_pos
-- name    : FastCLO.LowerBound.rho_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:11.123989+00:00
-- url     : https://prove2.me/theorems/66f1ef7f-aa3d-4f93-a902-f8be01e947e3
-- title:
--   Theorem 3 (parenthetical) — ρ(Z) > 0 for a polytope with at least two extreme points
-- statement:
--   Let $\mathcal Z$ be a polytope whose set of extreme points $\mathcal Z^\angle$ contains at least two points, and let $\rho(\mathcal Z)$ be its vertex separation. Then
--   $$\rho(\mathcal Z) = \inf_{z\in\mathcal Z^\angle,\ z'\in\mathrm{conv}(\mathcal Z^\angle\setminus\{z\})} \|z - z'\| > 0.$$
--
--   The paper records this as "positive by definition" when it introduces $\rho(\mathcal Z)$. Positivity is what makes the noise parameter $\gamma = B/\rho(\mathcal Z)$ of Theorem 7 finite and the lower bound non-trivial.
--
--   **Formalization Note** The hypothesis "at least two extreme points" makes the infimum range over a nonempty set; with one extreme point Lean's value of the empty infimum is $0$. That a polytope has finitely many extreme points is part of what has to be proved, not an assumption.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Theorem 3, p. 7 (parenthetical after the definition of ρ(Z))

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model
import Definitions.Def_FastCLO_LowerBound_Rho

namespace FastCLO.LowerBound

/-- `ρ(Z) > 0` (Hu, Kallus, Mao, arXiv:2011.03030v3, Theorem 3, p. 7, the parenthetical "which is
positive by definition"): for a polytope `Z` with at least two extreme points, the smallest distance
from an extreme point to the convex hull of the other extreme points is positive.

Formalization Note: `P.ext.Nontrivial` (two distinct extreme points) makes the infimum range over a
nonempty set; with one extreme point `ρ(Z)` is `sInf ∅ = 0` in Lean and the paper's claim is
vacuous there. Finiteness of `Z∠` is a property of polytopes, not a hypothesis. -/
theorem rho_pos {d : ℕ} (P : Polytope d) (h : P.ext.Nontrivial) : 0 < rho P := by sorry

end FastCLO.LowerBound
