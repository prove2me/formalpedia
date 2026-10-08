-- Prove2me | Theorems.Thm_DiffVI_Cone_prop_8_3
-- name    : DiffVI.Cone.prop_8_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:12.024985+00:00
-- url     : https://prove2.me/theorems/487135cf-def0-42e9-b7c3-362dfbd69c74
-- title:
--   Proposition 8.3, p. 59 — for a cone K the step (8.4) is uniquely solvable, and ‖u^h‖ obeys the bound (8.10), corrected
-- statement:
--   Let $K$ be a closed convex cone in $\mathbb R^m$ and $\theta\in[0,1]$. Let $(f,B,G)$ satisfy (A), (B) and (D), with constants $L_f,L_B,L_G,\rho_f,\sigma_B,\eta_G$ as in Proposition 8.2. Let $F=E^\top\circ\Psi\circ E$ satisfy (C′), assume $\Psi(0)=0$ and (E), let $Z$, $W$ be orthonormal bases of $\ker E$ and $(\ker E)^\perp$ and let $\eta_\Upsilon$ satisfy (8.7).
--
--   1. If $h$ satisfies (8.3), then for all $x^{\rm ref}\in\mathbb R^n$ and $t,t_{\rm ref}\in[0,T]$ there is a unique pair $(x^h,u^h)$ satisfying (8.4).
--   2. There are constants $\xi>0$ and $\bar h>0$ such that, whenever $0<h<\bar h$, $h$ satisfies (8.3) and
--   $$0<h<\frac{\eta_\Upsilon}{\|W\|^2L_G\sigma_B\big(1+L_G\sigma_B/\eta_G\big)},\tag{8.9}$$
--   and $u^{\rm ref}\in K$ is such that $G(t_{\rm ref},x^{\rm ref})+F(u^{\rm ref})\in K^*$, every pair $(x^h,u^h)$ satisfying (8.4) obeys
--   $$\|u^h\|\le\xi\Big[\Big(1+\frac1h\Big)|t-t_{\rm ref}|+\|G(t,x^{\rm ref})\|+\|f(t,x^{\rm ref})\|+\|x^h-x^{\rm ref}\|\Big].$$
--   The constant $\xi$ does not depend on $h$, $x^{\rm ref}$, $t$ or $t_{\rm ref}$.
--
--   This is the uniform bound on the multiplier $u^h$ that drives the a priori estimates of Theorem 8.1.
--
--   **Formalization Note** The printed bound (8.10) has $h\{\|f(t,x^{\rm ref})\|+\|x^h-x^{\rm ref}\|\}$ in place of $\|f(t,x^{\rm ref})\|+\|x^h-x^{\rm ref}\|$, and is false: with $n=m=1$, $K=\mathbb R_+$, $E=0$, $\Psi=\mathrm{id}$, $G(t,x)=x$, $B\equiv1$, $f\equiv-1$, $\theta=1$, $x^{\rm ref}=0$, $u^{\rm ref}=0$, $t=t_{\rm ref}$, all hypotheses hold, $(x^h,u^h)=(0,1)$ satisfies (8.4), and the printed right-hand side is $\xi h<1$ for small $h$. The statement here drops that factor $h$, which is what the paper's own estimates (8.13) and the bound on $\|\lambda^h\|$ on p. 60 yield; the page's "$|t-t'|$" is read as $|t-t_{\rm ref}|$. (8.3) and (8.9) are multiplied out so that vanishing denominators impose no restriction. "$h$ sufficiently small" is the threshold $\bar h$, chosen together with $\xi$.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 59, Proposition 8.3, (8.9), (8.10) (corrected); pp. 59–60, (8.11)–(8.13)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem prop_8_3 {n m ℓ k p : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf LB LG ρf σB : ℝ) (hf : DiffVI.Exist.LipOnΩ T f Lf) (hBL : DiffVI.Exist.LipOnΩ T B LB) (hG : DiffVI.Exist.LipOnΩ T G LG)
    (hρf : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖f t x‖ ≤ ρf * (1 + ‖x‖))
    (hσB : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖B t x‖ ≤ σB)
    (ηG : ℝ) (hD : CondD T B G ηG)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ))
    (hC' : CondC' F E Ψ) (hΨ0 : Ψ 0 = 0) (hE : CondE K E)
    (Z : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (W : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hZW : IsZWBasis E Z W) (ηΥ : ℝ) (hΥ : CondUps E W Ψ ηΥ) :
    (∀ h : ℝ, 0 < h → h * (1 - θ) * Lf * (LG * σB + ηG) < ηG → h * (1 - θ) * ρf < 1 →
      ∀ xref : EuclideanSpace ℝ (Fin n), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T,
        ∃ xh uh, IsStep K f B G F θ h t tref xref xh uh ∧
          ∀ xh' uh', IsStep K f B G F θ h t tref xref xh' uh' → xh' = xh ∧ uh' = uh) ∧
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ h2 : ℝ, 0 < h2 ∧
      ∀ h : ℝ, 0 < h → h < h2 →
        h * (1 - θ) * Lf * (LG * σB + ηG) < ηG → h * (1 - θ) * ρf < 1 →
        h * (‖W‖ ^ 2 * LG * σB * (1 + LG * σB / ηG)) < ηΥ →
        ∀ xref : EuclideanSpace ℝ (Fin n), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T,
          ∀ uref ∈ K, G tref xref + F uref ∈ DiffVI.Exist.dualCone K →
            ∀ xh uh, IsStep K f B G F θ h t tref xref xh uh →
              ‖uh‖ ≤ ξ * ((1 + 1 / h) * |t - tref| + ‖G t xref‖ + ‖f t xref‖ + ‖xh - xref‖) := by sorry

end DiffVI.Cone
