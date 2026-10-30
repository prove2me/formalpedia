-- Prove2me | Theorems.Thm_ExactPenGNEP_NonShared_theorem_11_descent_bound
-- name    : ExactPenGNEP.NonShared.theorem_11_descent_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T03:54:20.488046+00:00
-- url     : https://prove2.me/theorems/54b32e93-b512-42c9-bdeb-0dda54b3a720
-- title:
--   Proof of Theorem 11, p. 18, first display — the ℓq residual decreases at rate α c_q^{q−1} along the Slater direction
-- statement:
--   Consider the finitely representable coupled sets (16) with functions $g^{\hat\nu}_i$ and affine functions $h^{\hat\nu}_j$ of the profile, and the $\ell_q$ residual $r_{\hat\nu;q}$ of player $\hat\nu$, $q \in (1, \infty)$. Fix a profile $x$ and a player $\hat\nu$ with $x^{\hat\nu} \notin X^{\hat\nu}(x^{-\hat\nu})$, such that each $g^{\hat\nu}_i(\cdot, x^{-\hat\nu})$ is differentiable. Let $\alpha > 0$ and let $\hat x^{\hat\nu} \in \mathbb R^{n_{\hat\nu}}$ satisfy
--
--   1. $\nabla_{x^{\hat\nu}} g^{\hat\nu}_i(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha$ whenever $g^{\hat\nu}_i(x) > 0$, and
--   2. $[\operatorname{sgn} h^{\hat\nu}_j(x)]\, \nabla_{x^{\hat\nu}} h^{\hat\nu}_j(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha$ whenever $h^{\hat\nu}_j(x) \ne 0$.
--
--   Let $c_q > 0$ satisfy $c_q \|v\|_q \le \|v\|_{q-1}$ for all vectors $v$ of every dimension. Then
--
--   $$\nabla_{x^{\hat\nu}} r_{\hat\nu;q}(x)^T(\hat x^{\hat\nu} - x^{\hat\nu}) \le -\alpha \left( \frac{r_{\hat\nu,q-1}(x)}{r_{\hat\nu,q}(x)} \right)^{q-1} \le -\alpha\, c_q^{q-1},$$
--
--   where $r_{\hat\nu,q-1}$ is the same residual with exponent $q - 1$.
--
--   In the proof of Theorem 11 (b) this is applied at an infeasible penalized equilibrium $x^*$: it gives a uniform rate of decrease of the penalty term along the Slater direction.
--
--   **Formalization Note** The middle equality of the paper's display, which expands the gradient by (5), is the separate milestone for Equation (5) and is not repeated. The partial gradient applied to a direction is the Fréchet derivative of the function of player $\hat\nu$'s block. The bound does not use that $x$ is an equilibrium, so it is stated for any profile $x$ with $x^{\hat\nu} \notin X^{\hat\nu}(x^{-\hat\nu})$.
-- source:
--   Ba & Pang, Exact penalization of generalized Nash equilibrium problems, arXiv:1811.10674v2, p. 18, proof of Theorem 11, first display

import Mathlib
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_ExactPenGNEP_NonShared_Setting

open LeiBR.Sync

namespace ExactPenGNEP.NonShared

theorem theorem_11_descent_bound {N : ℕ} {n m p : Fin N → ℕ}
    (g : ∀ ν, Fin (m ν) → Profile n → ℝ) (h : ∀ ν, Fin (p ν) → Profile n →ᵃ[ℝ] ℝ)
    (q α c : ℝ) (x : Profile n) (νh : Fin N) (xh : Strat n νh)
    (hq : 1 < q) (hα : 0 < α)
    (hg_diff : ∀ i, Differentiable ℝ (fun y => g νh i (Function.update x νh y)))
    (hx : x νh ∉ frSet g h νh x)
    (hg_bullet : ∀ i, 0 < g νh i x →
      fderiv ℝ (fun y => g νh i (Function.update x νh y)) (x νh) (xh - x νh) ≤ -α)
    (hh_bullet : ∀ j, h νh j x ≠ 0 →
      Real.sign (h νh j x) *
        fderiv ℝ (fun y => h νh j (Function.update x νh y)) (x νh) (xh - x νh) ≤ -α)
    (hc : 0 < c)
    (hcq : ∀ (k : ℕ) (v : Fin k → ℝ),
      c * (∑ i, |v i| ^ q) ^ (1 / q) ≤ (∑ i, |v i| ^ (q - 1)) ^ (1 / (q - 1))) :
    fderiv ℝ (fun y => lqRes (g νh) (fun j z => h νh j z) q (Function.update x νh y)) (x νh)
        (xh - x νh)
      ≤ -α * (lqRes (g νh) (fun j z => h νh j z) (q - 1) x /
          lqRes (g νh) (fun j z => h νh j z) q x) ^ (q - 1) ∧
    -α * (lqRes (g νh) (fun j z => h νh j z) (q - 1) x /
          lqRes (g νh) (fun j z => h νh j z) q x) ^ (q - 1) ≤ -α * c ^ (q - 1) := by sorry

end ExactPenGNEP.NonShared
