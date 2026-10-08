-- Prove2me | Theorems.Thm_AdamDyn_DecConv_proposition_7_15
-- name    : AdamDyn.DecConv.proposition_7_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:10:21.205365+00:00
-- url     : https://prove2.me/theorems/8a2353be-f28d-44f7-a529-e3c3234d3970
-- title:
--   Proposition 7.15 — $W_\delta$ is a strict Lyapunov function of the Adam semiflow restricted to a compact hull
-- statement:
--   Under Assumptions 2.3, 2.4, 7.1 and 7.2, with $0 < b \le 4a$ and $\varepsilon > 0$, let $\Phi$ be the semiflow (7.8) of $(\mathrm{ODE}_\infty)$ on $\mathcal Z_+$. Let $K \subset \mathcal Z_+$ be compact and define
--   $$ K' = \overline{\{ \Phi(t, z) : t \ge 0,\ z \in K\}} .$$
--   Let $\bar\Phi : [0, +\infty) \times K' \to K'$ be the restriction of $\Phi$ to $K'$. Then:
--
--   1. $K'$ is compact;
--   2. $\bar\Phi$ is well defined (takes values in $K'$) and is a semiflow on $K'$;
--   3. the set of equilibrium points of $\bar\Phi$ is $\mathcal E \cap K'$;
--   4. there exists $\delta > 0$ such that $W_\delta$ is a strict Lyapunov function for $\bar\Phi$.
--
--   **Formalization Note** Points ii)–iv) are stated as: there is a semiflow $\bar\Phi$ on $K'$ with $\bar\Phi_t(z) = \Phi_t(z)$ for all $t$ and $z \in K'$, whose equilibria are $\mathcal E \cap K'$ and for which some $W_\delta$, $\delta > 0$, is a strict Lyapunov function. The closure is taken in $\mathcal Z_+$, which is closed in $\mathcal Z$.
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 18, Eq. (7.9), the set ℰ, Proposition 7.15

import Mathlib
import Definitions.Def_AdamDyn_ODEConv_StrictLyapunov
import Definitions.Def_AdamDyn_DecConv_ODEInf
import Definitions.Def_AdamDyn_ODEConv_LyapunovW

open Filter Topology
open scoped NNReal

namespace AdamDyn.DecConv

/-- Proposition 7.15 (Barakat & Bianchi, arXiv:1810.02263v4, p. 18). Let Assumptions 2.3, 2.4,
7.1 and 7.2 hold and `0 < b ≤ 4a`; let `Φ` be the semiflow (7.8) of `(ODE∞)` on `𝒵₊`. Let
`K ⊂ 𝒵₊` be compact and `K′ := cl{Φ(t, z) : t ≥ 0, z ∈ K}`. Then i) `K′` is compact;
ii) the restriction `Φ̄` of `Φ` to `K′` is well defined and is a semiflow on `K′`; iii) the set of
equilibrium points of `Φ̄` is `ℰ ∩ K′`; iv) there is `δ > 0` such that `W_δ` is a strict Lyapunov
function for `Φ̄`. -/
theorem proposition_7_15 {d : ℕ} (a b ε : ℝ) (F : AdamDyn.WellPosed.Vec d → ℝ) (S : AdamDyn.WellPosed.Vec d → AdamDyn.WellPosed.Vec d)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (hcoer : Tendsto F (cocompact (AdamDyn.WellPosed.Vec d)) atTop)
    (hb : 0 < b) (hba : b ≤ 4 * a) (hε : 0 < ε)
    (Φ : Flow ℝ≥0 (AdamDyn.ODEConv.Zplus d)) (hΦ : AdamDyn.ODEConv.IsODEInfSemiflow a b ε F S Φ)
    (K : Set (AdamDyn.ODEConv.Zplus d)) (hK : IsCompact K)
    (K' : Set (AdamDyn.ODEConv.Zplus d)) (hK' : K' = closure {w | ∃ t : ℝ≥0, ∃ z ∈ K, Φ t z = w}) :
    IsCompact K' ∧
      ∃ Φbar : Flow ℝ≥0 K', (∀ (t : ℝ≥0) (z : K'), ((Φbar t z : K') : AdamDyn.ODEConv.Zplus d) = Φ t z) ∧
        AdamDyn.ODEConv.equilibria Φbar = {z : K' | (z : AdamDyn.ODEConv.Zplus d).1 ∈ AdamDyn.ODEConv.equilibriumSet F S} ∧
        ∃ δ : ℝ, 0 < δ ∧
          AdamDyn.ODEConv.IsStrictLyapunovFunction Φbar
            (fun z : K' => AdamDyn.ODEConv.Wdelta a ε δ F S (z : AdamDyn.ODEConv.Zplus d).1) := by sorry

end AdamDyn.DecConv
