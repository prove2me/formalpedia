-- Prove2me | Theorems.Thm_FastCLO_LowerBound_eq_25
-- name    : FastCLO.LowerBound.eq_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:23:06.759311+00:00
-- url     : https://prove2.me/theorems/bea16a5e-e74b-47c1-be1a-df9a39f5fabf
-- title:
--   Eq. (25) — the direction w(z) = (ρ(Z)/‖z̄ − z‖²)(z̄ − z) has norm ≤ 1 and separates z from the other vertices by exactly ρ(Z)
-- statement:
--   Let $\mathcal Z$ be a polytope with at least two extreme points, let $z \in \mathcal Z^\angle$, and let $\bar z$ be the Euclidean projection of $z$ onto $\mathrm{conv}(\mathcal Z^\angle\setminus\{z\})$, i.e. a point of that hull with $\|z - \bar z\| \le \|z - y\|$ for every $y$ in it. Define
--   $$w(z) = \frac{\rho(\mathcal Z)}{\|\bar z - z\|^2}\,(\bar z - z).$$
--   Then $\|w(z)\| \le 1$ and
--   $$\min_{z'\in\mathcal Z^\angle\setminus\{z\}} w(z)^\top (z' - z) = \rho(\mathcal Z).$$
--
--   With $f^*(x) = \zeta\, w(z)$, the vertex $z$ is the unique optimal decision and every other vertex costs at least $\zeta\rho(\mathcal Z)$ more, with equality for some vertex; this is how the hard instances of Theorem 7 achieve a prescribed gap $\Delta$ with cost vectors of norm at most one.
--
--   **Formalization Note** The projection is specified by its defining nearest-point property instead of being constructed. The minimum is stated as two facts: $w(z)^\top(z'-z) \ge \rho(\mathcal Z)$ for every $z' \in \mathcal Z^\angle\setminus\{z\}$, and equality for some such $z'$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, proof of Theorem 7 (A.4.4), Eq. (25), p. 28

import Mathlib
import Definitions.Def_FastCLO_LowerBound_Model
import Definitions.Def_FastCLO_LowerBound_Rho

open scoped InnerProductSpace

namespace FastCLO.LowerBound

/-- Eq. (25) (Hu, Kallus, Mao, arXiv:2011.03030v3, proof of Theorem 7, p. 28): for an extreme
point `z` of `Z` with projection `z̄` onto `conv(Z∠∖{z})`, the vector
`w(z) = (ρ(Z)/‖z̄ − z‖²)(z̄ − z)` has `‖w(z)‖ ≤ 1` and
`min_{z'∈Z∠∖{z}} w(z)ᵀ(z' − z) = ρ(Z)`.

Formalization Note: the projection is given by its defining property (`zbar` lies in the hull and is
a nearest point of it to `z`) instead of being constructed. "min … = ρ(Z)" is stated as a lower bound
for every `z' ∈ Z∠∖{z}` together with attainment. -/
theorem eq_25 {d : ℕ} (P : Polytope d) (hnt : P.ext.Nontrivial) (z : Vec d) (hz : z ∈ P.ext)
    (zbar : Vec d) (hzbar : zbar ∈ convexHull ℝ (P.ext \ {z}))
    (hproj : ∀ y ∈ convexHull ℝ (P.ext \ {z}), ‖z - zbar‖ ≤ ‖z - y‖) :
    let w : Vec d := (rho P / ‖zbar - z‖ ^ 2) • (zbar - z)
    ‖w‖ ≤ 1 ∧ (∀ z' ∈ P.ext \ {z}, rho P ≤ ⟪w, z' - z⟫_ℝ) ∧
      ∃ z' ∈ P.ext \ {z}, ⟪w, z' - z⟫_ℝ = rho P := by sorry

end FastCLO.LowerBound
