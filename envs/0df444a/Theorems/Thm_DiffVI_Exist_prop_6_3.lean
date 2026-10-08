-- Prove2me | Theorems.Thm_DiffVI_Exist_prop_6_3
-- name    : DiffVI.Exist.prop_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:19.624353+00:00
-- url     : https://prove2.me/theorems/a3d72424-61f3-4a92-a5ec-7121af3cd2e0
-- title:
--   Proposition 6.3, p. 33 — for F = Eᵀ∘Ψ∘E with Ψ strongly monotone on EK and K∞ ∩ ker E = {0}, SOL(K, r + F) is nonempty, convex, with (6.5)
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a nonempty closed convex set. Let $F=E^T\circ\Psi\circ E$, where $E\in\mathbb R^{\ell\times m}$ and $\Psi:\mathbb R^\ell\to\mathbb R^\ell$ is continuous and strongly monotone on $EK$: for some $\eta_\Psi>0$,
--   $$(u'-u)^T(\Psi(u')-\Psi(u))\ge\eta_\Psi\|u'-u\|^2\qquad\forall u,u'\in EK.$$
--   If $K_\infty\cap\ker E=\{0\}$, then $\mathrm{SOL}(K,r+F)$ is a nonempty convex set for every $r\in\mathbb R^m$, and there is $\rho>0$ with $\|u\|\le\rho(1+\|r\|)$ for all $r\in\mathbb R^m$ and $u\in\mathrm{SOL}(K,r+F)$.
--
--   This covers case (b) of Theorem 6.1: a strongly monotone composite map need not be coercive in the sense of (6.6), yet its VI solutions grow linearly.
--
--   **Formalization Note** $E^T$ is the adjoint of $E$ as a linear map between Euclidean spaces.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 33, Proposition 6.3 (and p. 32 for strongly monotone composite maps)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Proposition 6.3, p. 33: for a strongly monotone composite `F = Eᵀ ∘ Ψ ∘ E` with
`K∞ ∩ ker E = {0}`, `SOL(K, r + F)` is nonempty and convex for every `r`, and (6.5) holds for all
`r ∈ ℝᵐ`. -/
theorem prop_6_3 {m ℓ : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
    (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ)) (hΨc : Continuous Ψ)
    (η : ℝ) (hΨ : IsStronglyMonotoneOn Ψ (E '' K) η)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hF : ∀ u, F u = (E†) (Ψ (E u)))
    (hker : recCone K ∩ {v | E v = 0} = {0}) :
    (∀ r : EuclideanSpace ℝ (Fin m),
      (SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K).Nonempty ∧
      Convex ℝ (SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K)) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ r : EuclideanSpace ℝ (Fin m),
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K, ‖u‖ ≤ ρ * (1 + ‖r‖)) := by sorry

end DiffVI.Exist
