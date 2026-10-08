-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_proposition_7_13
-- name    : AdamDyn.ODEConv.proposition_7_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:11:18.311981+00:00
-- url     : https://prove2.me/theorems/b1676ee3-ffb9-4f74-b9b2-4dc58ae9ccac
-- title:
--   Proposition 7.13 — (ODE$_\infty$) is well posed on $\mathcal Z_+$ and defines a semiflow $\Phi$
-- statement:
--   Under Assumptions 2.3, 2.4, 7.1 and 7.2, with $0 < b \le 4a$ and $\varepsilon > 0$:
--
--   1. for every $z_0 \in \mathcal Z_+$ there exists a global solution of $\dot z = h_\infty(z)$ with $z(0) = z_0$;
--   2. any two such global solutions coincide on $[0, +\infty)$;
--   3. the map
--   $$\Phi : [0, +\infty) \times \mathcal Z_+ \to \mathcal Z_+, \qquad (t, z) \mapsto Z^\infty_\infty(z)(t) \tag{7.8}$$
--   is a semiflow: there is a semiflow on $\mathcal Z_+$ whose orbit from each $z_0$ is the global solution of $(\mathrm{ODE}_\infty)$ from $z_0$.
--
--   Every other statement of the mission about $\Phi$ assumes that $\Phi$ is this semiflow.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 17, Proposition 7.13 and Eq. (7.8)

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open Filter Topology
open scoped NNReal

namespace AdamDyn.ODEConv

/-- Proposition 7.13 (Barakat & Bianchi, arXiv:1810.02263v4, p. 17). Let Assumptions 2.3, 2.4,
7.1 and 7.2 hold and `0 < b ≤ 4a`. There is a unique global solution to `(ODE∞)` starting from
any given point of `𝒵₊` (uniqueness on `[0, +∞)`), and the map
`Φ : [0, +∞) × 𝒵₊ → 𝒵₊, (t, z) ↦ Z^∞_∞(z)(t)` of (7.8) is a semiflow. -/
theorem proposition_7_13 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε) :
    (∀ z0 : AdamDyn.WellPosed.State d, (∀ i, 0 ≤ z0.2.2 i) → ∃ z : ℝ → AdamDyn.WellPosed.State d, IsSolutionInf a b ε F S ⊤ z0 z) ∧
    (∀ z0 : AdamDyn.WellPosed.State d, (∀ i, 0 ≤ z0.2.2 i) → ∀ z z' : ℝ → AdamDyn.WellPosed.State d,
      IsSolutionInf a b ε F S ⊤ z0 z → IsSolutionInf a b ε F S ⊤ z0 z' →
        Set.EqOn z z' (Set.Ici 0)) ∧
    ∃ Φ : Flow ℝ≥0 (Zplus d), IsODEInfSemiflow a b ε F S Φ := by sorry

end AdamDyn.ODEConv
