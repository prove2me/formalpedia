-- Prove2me | Theorems.Thm_AdamDyn_WellPosed_lemma_7_4
-- name    : AdamDyn.WellPosed.lemma_7_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:06:36.064248+00:00
-- url     : https://prove2.me/theorems/af7a9d3a-be99-49f7-8b94-9407ea9483e1
-- title:
--   Lemma 7.4 — solutions enter the open orthant $\mathcal Z_+^*$ immediately
-- statement:
--   Let $a, b, \varepsilon > 0$, let $F : \mathbb R^d \to \mathbb R$ be continuously differentiable with locally Lipschitz gradient (Assumption 7.1), and let $S : \mathbb R^d \to \mathbb R^d$ be locally Lipschitz (Assumption 7.2) with $S(x) > 0$ coordinatewise for every $x$ (Assumption 2.4). Let $\eta \in [0,+\infty]$, $T \in (0,+\infty]$, $z_0 \in \mathcal Z_+$, and let $z \in Z^\eta_T(z_0)$ be a solution of $(\mathrm{ODE}_\eta)$ on $[0,T)$ with initial condition $z_0$. Then
--   $$z\big((0,T)\big) \subset \mathcal Z_+^* = \mathbb R^d \times \mathbb R^d \times (0,+\infty)^d ,$$
--   that is, every coordinate $v_i(t)$ of the third block is strictly positive for $0 < t < T$.
--
--   Solutions are a priori only $\mathcal Z$-valued (the field is extended to negative $v$ through $|v|$); this lemma shows that they stay in the region where the Adam field and the Lyapunov functions are smooth.
--
--   **Formalization Note.** $\eta = +\infty$ means the autonomous field $h_\infty$ (7.1).
-- source:
--   Barakat & Bianchi, Convergence and Dynamical Behavior of the ADAM Algorithm for Nonconvex Stochastic Optimization, arXiv:1810.02263v4, p. 12, Lemma 7.4

import Mathlib
import Definitions.Def_AdamDyn_WellPosed_adamField

open scoped NNReal

namespace AdamDyn.WellPosed

/-- Lemma 7.4 (p. 12). Under Assumptions 2.4, 7.1, 7.2: for every `η ∈ [0, +∞]`, `T ∈ (0, +∞]`,
`z0 ∈ 𝒵₊` and `z ∈ Z^η_T(z0)`, one has `z((0, T)) ⊂ 𝒵₊*`. -/
theorem lemma_7_4 {d : ℕ} (a b ε : ℝ) (F : Vec d → ℝ) (S : Vec d → Vec d)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hF : ContDiff ℝ 1 F) (hgradF : LocallyLipschitz (gradient F))
    (hS : LocallyLipschitz S) (hSpos : ∀ x i, 0 < S x i)
    (η : WithTop ℝ≥0) (T : WithTop ℝ) (hT : 0 < T) (z0 : State d) (hz0 : z0 ∈ Zplus)
    (z : ℝ → State d) (hz : IsSolutionOn a b ε F S η T z0 z) :
    ∀ t ∈ timeIoo T, z t ∈ ZplusStar := by sorry

end AdamDyn.WellPosed
