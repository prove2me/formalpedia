-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_theorem_11_first_order
-- name    : ExactPenGNEP.NonShared.theorem_11_first_order
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:31.752985+00:00
-- url     : https://prove2.me/theorems/a89bf3fd-7f6c-4bfb-8ea1-73f28429a493
-- title:
--   Proof of Theorem 11, p. 18, second display — first-order inequality at a penalized best response
-- statement:
--   Let $C^{\hat\nu} \subseteq \mathbb R^{n_{\hat\nu}}$ be convex, fix a profile $x^*$, and suppose that $\theta_{\hat\nu}(\cdot, x^{*,-\hat\nu})$ is convex and Lipschitz continuous on $C^{\hat\nu}$ with constant $\mathrm{Lip}_\theta > 0$. Let the coupled set $X^{\hat\nu}(x^{*,-\hat\nu})$ be given by (16) with each $g^{\hat\nu}_i(\cdot, x^{*,-\hat\nu})$ differentiable and $h^{\hat\nu}$ affine, let $q \in (1,\infty)$, $\rho > 0$, and suppose $x^{*,\hat\nu} \notin X^{\hat\nu}(x^{*,-\hat\nu})$. If
--
--   $$x^{*,\hat\nu} \in \operatorname*{argmin}_{x^{\hat\nu} \in C^{\hat\nu}} \ \theta_{\hat\nu}(x^{\hat\nu}, x^{*,-\hat\nu}) + \rho\, r_{\hat\nu;q}(x^{\hat\nu}, x^{*,-\hat\nu}),$$
--
--   then for every $\hat x^{\hat\nu} \in C^{\hat\nu}$, the directional derivative $\theta_{\hat\nu}(\cdot, x^{*,-\hat\nu})'(x^{*,\hat\nu}; \hat x^{\hat\nu} - x^{*,\hat\nu})$ of (3) exists and
--
--   $$0 \le \theta_{\hat\nu}(\cdot, x^{*,-\hat\nu})'(x^{*,\hat\nu}; \hat x^{\hat\nu} - x^{*,\hat\nu}) + \rho\, \nabla_{x^{\hat\nu}} r_{\hat\nu;q}(x^*)^T(\hat x^{\hat\nu} - x^{*,\hat\nu}), \qquad \theta_{\hat\nu}(\cdot, x^{*,-\hat\nu})'(x^{*,\hat\nu}; \hat x^{\hat\nu} - x^{*,\hat\nu}) \le \mathrm{Lip}_\theta \|\hat x^{\hat\nu} - x^{*,\hat\nu}\|_2.$$
--
--   Combined with the descent bound of the first display, this yields $0 \le \mathrm{Lip}_\theta \|\hat x^{\hat\nu} - x^{*,\hat\nu}\|_2 - \rho\alpha c_q^{q-1}$, which is impossible for large $\rho$.
--
--   **Formalization Note** The page writes the minimization over $C^{\hat\nu} \cap X^{\hat\nu}(x^{*,-\hat\nu})$. This is a misprint: in the penalized NEP displayed on p. 17 each player minimizes over $C^\nu$ only, and with the intersection the point $\hat x^{\hat\nu}$ would not be admissible. The statement uses $C^{\hat\nu}$. The directional derivative (3) is the one-sided limit as $\tau \downarrow 0$ of the difference quotient, stated as the existence of the limit $\theta'$. The term $-\rho\alpha c_q^{q-1}$ and the final rewriting with $\hat\alpha$ are not part of this item: the former is the descent-bound milestone, the latter a rewriting.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, p. 18, proof of Theorem 11, second display; Equation (3), p. 5

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open Filter Topology LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem theorem_11_first_order {N : ℕ} {n m p : Fin N → ℕ} (C : ∀ ν, Set (Strat n ν))
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (θ : Fin N → Profile n → ℝ) (Lip q ρ : ℝ) (xs : Profile n) (νh : Fin N) (xh : Strat n νh)
    (hCv : Convex ℝ (C νh)) (hLip : 0 < Lip)
    (hθ_cvx : ConvexOn ℝ (C νh) (fun y => θ νh (Function.update xs νh y)))
    (hθ_lip : LipschitzOnWith (Real.toNNReal Lip) (fun y => θ νh (Function.update xs νh y)) (C νh))
    (hg_diff : ∀ i, Differentiable ℝ (fun y => g νh i (Function.update xs νh y)))
    (hq : 1 < q) (hx : xs νh ∉ frSet g h νh xs) (hρ : 0 < ρ) (hmem : xs νh ∈ C νh)
    (hmin : ∀ y ∈ C νh,
      θ νh xs + ρ * lqRes (g νh) (fun j z => h νh j z) q xs ≤
        θ νh (Function.update xs νh y) +
          ρ * lqRes (g νh) (fun j z => h νh j z) q (Function.update xs νh y))
    (hxh : xh ∈ C νh) :
    ∃ θ' : ℝ,
      Tendsto (fun τ : ℝ => (θ νh (Function.update xs νh (xs νh + τ • (xh - xs νh))) - θ νh xs) / τ)
        (𝓝[>] 0) (𝓝 θ') ∧
      0 ≤ θ' + ρ * fderiv ℝ (fun y => lqRes (g νh) (fun j z => h νh j z) q
          (Function.update xs νh y)) (xs νh) (xh - xs νh) ∧
      θ' ≤ Lip * ‖xh - xs νh‖ := by sorry

end ExactPenGNEP.NonShared
