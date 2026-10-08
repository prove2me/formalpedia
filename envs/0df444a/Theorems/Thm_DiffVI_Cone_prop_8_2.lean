-- Prove2me | Theorems.Thm_DiffVI_Cone_prop_8_2
-- name    : DiffVI.Cone.prop_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:15.116831+00:00
-- url     : https://prove2.me/theorems/984a3153-339c-47ff-a260-6de4cd59ad0f
-- title:
--   Proposition 8.2, p. 54 — under (A)–(D) and (8.3), the step (8.4) has a solution, unique if F is monotone on K
-- statement:
--   Let $\emptyset\ne K\subseteq\mathbb R^m$ be closed and convex, $\theta\in[0,1]$, $T>0$. Let $f$, $B$, $G$ satisfy (A) with Lipschitz constants $L_f$, $L_B$, $L_G$ on $\Omega=[0,T]\times\mathbb R^n$, let $\|f(t,x)\|\le\rho_f(1+\|x\|)$ and $\|B(t,x)\|\le\sigma_B$ on $\Omega$, let $F$ satisfy (C) and let $(B,G)$ satisfy (D) with constant $\eta_G$. If
--   $$0<h<\min\left(\frac{\eta_G}{(1-\theta)L_f(L_G\sigma_B+\eta_G)},\ \frac{1}{(1-\theta)\rho_f}\right),\tag{8.3}$$
--   then for all $t,t_{\rm ref}\in[0,T]$ and $x^{\rm ref}\in\mathbb R^n$ there is a pair $(x^h,u^h)$ with
--   $$x^h=x^{\rm ref}+h\big[f(t,\theta x^{\rm ref}+(1-\theta)x^h)+B(t_{\rm ref},x^{\rm ref})u^h\big],\qquad u^h\in\mathrm{SOL}(K,G(t,x^h)+F).\tag{8.4}$$
--   If moreover $F$ is monotone on $K$, the pair is unique.
--
--   This is the well-posedness of one step of the time-stepping scheme (7.2): it makes the iterates well defined for all small steps.
--
--   **Formalization Note** (8.3) is multiplied out: $h(1-\theta)L_f(L_G\sigma_B+\eta_G)<\eta_G$ and $h(1-\theta)\rho_f<1$, so that a vanishing denominator (e.g. $\theta=1$) means no restriction, as the page's $1/0=\infty$ intends. The constants $L_f,L_B,L_G,\rho_f,\sigma_B$ are any constants for which the stated bounds hold; the growth bound on $f$ is the paper's (6.3), a consequence of (A).
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 54, Proposition 8.2, (8.3), (8.4)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem prop_8_2 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty) (hKcl : IsClosed K)
    (hKcv : Convex ℝ K) (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (Lf LB LG ρf σB : ℝ) (hf : DiffVI.Exist.LipOnΩ T f Lf) (hBL : DiffVI.Exist.LipOnΩ T B LB) (hG : DiffVI.Exist.LipOnΩ T G LG)
    (hρf : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖f t x‖ ≤ ρf * (1 + ‖x‖))
    (hσB : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : EuclideanSpace ℝ (Fin n), ‖B t x‖ ≤ σB)
    (hC : CondC K F) (ηG : ℝ) (hD : CondD T B G ηG)
    (h : ℝ) (hh : 0 < h) (h83a : h * (1 - θ) * Lf * (LG * σB + ηG) < ηG)
    (h83b : h * (1 - θ) * ρf < 1) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T, ∀ xref : EuclideanSpace ℝ (Fin n),
      ∃ xh uh, IsStep K f B G F θ h t tref xref xh uh) ∧
    (DiffVI.Exist.IsMonotoneOn F K →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ tref ∈ Set.Icc (0 : ℝ) T, ∀ xref : EuclideanSpace ℝ (Fin n),
        ∀ xh xh' : EuclideanSpace ℝ (Fin n), ∀ uh uh' : EuclideanSpace ℝ (Fin m),
          IsStep K f B G F θ h t tref xref xh uh → IsStep K f B G F θ h t tref xref xh' uh' → xh = xh' ∧ uh = uh') := by sorry

end DiffVI.Cone
