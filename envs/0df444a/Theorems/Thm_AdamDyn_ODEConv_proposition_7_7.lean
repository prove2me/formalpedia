-- Prove2me | Theorems.Thm_AdamDyn_ODEConv_proposition_7_7
-- name    : AdamDyn.ODEConv.proposition_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T21:13:06.431996+00:00
-- url     : https://prove2.me/theorems/c30425e0-3232-4b63-8a58-51e3fed86baf
-- title:
--   Proposition 7.7 — solutions of (ODE$_\infty$) from a compact set stay in a compact set
-- statement:
--   Under Assumptions 2.3, 2.4, 7.1 and 7.2 (as in Proposition 7.6), with $0 < b \le 4a$ and $\varepsilon > 0$: for every compact set $K \subset \mathcal Z_+$ there exists another compact set $K' \subset \mathcal Z_+$ such that for every $T \in (0, +\infty]$ and every solution $z \in Z^\infty_T(K) = \bigcup_{z_0 \in K} Z^\infty_T(z_0)$ of $\dot z = h_\infty(z)$,
--   $$ z\big([0, T)\big) \subset K' .$$
--
--   It gives the compact forward-invariant hull on which the autonomous system is studied.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 14, Proposition 7.7

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_AdamField

open Filter Topology
open scoped ENNReal

namespace AdamDyn.ODEConv

/-- Proposition 7.7 (Barakat & Bianchi, arXiv:1810.02263v4, p. 14). Let Assumptions 2.3, 2.4,
7.1 and 7.2 hold and `0 < b ≤ 4a`. For every compact `K ⊂ 𝒵₊` there is another compact
`K′ ⊂ 𝒵₊` such that for every `T ∈ (0, +∞]` and every `z ∈ Z^∞_T(K)`, `z([0, T)) ⊂ K′`. -/
theorem proposition_7_7 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (K : Set (AdamDyn.WellPosed.State d)) (hK : IsCompact K) (hKplus : ∀ w ∈ K, ∀ i, 0 ≤ w.2.2 i) :
    ∃ K' : Set (AdamDyn.WellPosed.State d), IsCompact K' ∧ (∀ w ∈ K', ∀ i, 0 ≤ w.2.2 i) ∧
      ∀ T : ℝ≥0∞, 0 < T → ∀ z0 ∈ K, ∀ z : ℝ → AdamDyn.WellPosed.State d, IsSolutionInf a b ε F S T z0 z →
        ∀ t ∈ timeIco T, z t ∈ K' := by sorry

end AdamDyn.ODEConv
