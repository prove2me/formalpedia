-- Prove2me | Theorems.Thm_DiffVI_Cone_eq_8_14
-- name    : DiffVI.Cone.eq_8_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:52.181223+00:00
-- url     : https://prove2.me/theorems/1396051e-1ded-4ba7-8f13-f47e56e739be
-- title:
--   (8.14), proof of Theorem 8.1, p. 61 — ‖u^{h,i+1}‖ ≤ ω(1 + ‖x^{h,i}‖ + h‖x^{h,i+1} − x^{h,i}‖) for all small h
-- statement:
--   Assume the hypotheses of Theorem 8.1: $K$ a closed convex cone, $\theta\in[0,1]$, $(f,B,G)$ satisfying (A), (B) and (D), $F=E^\top\circ\Psi\circ E$ satisfying (C′), $\Psi(0)=0$ and (E). There are a constant $\omega>0$ and an integer $N_1\ge1$ such that for every $x^0\in\mathbb R^n$, every $N\ge N_1$ (step $h=T/N$) and every run $\{(x^{h,i},u^{h,i})\}$ of the scheme (7.2) from $x^0$ whose initial multiplier satisfies $u^{h,0}\in\mathrm{SOL}(K,G(0,x^0)+F)$,
--   $$\|u^{h,i+1}\|\le\omega\big(1+\|x^{h,i}\|+h\|x^{h,i+1}-x^{h,i}\|\big),\qquad i=0,1,\dots,N-1.\tag{8.14}$$
--   The constant $\omega$ does not depend on $h$ or $x^0$.
--
--   Combined with the one-step bound $\|x^{h,i+1}-x^{h,i}\|\le h\rho_x(1+\|x^{h,i}\|+\|u^{h,i+1}\|)$, this is the linear growth of the multipliers in the state that yields the uniform bounds (7.5).
--
--   **Formalization Note** The step is $h=T/N$ and "$h$ sufficiently small" is $N\ge N_1$. The initial multiplier $u^{h,0}$ is an arbitrary element of $\mathrm{SOL}(K,G(0,x^0)+F)$, as in the proof on p. 61. The page derives (8.14) from the printed (8.10), which is false (see Proposition 8.3); (8.14) itself remains true for small $h$, via the corrected bound.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 61, (8.14), proof of Theorem 8.1

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Cone_Setting

open scoped InnerProductSpace InnerProduct
open SolodovSvaiterVI.Alg21

namespace DiffVI.Cone

theorem eq_8_14 {n m ℓ : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hK : IsClosedConvexCone K)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : DiffVI.Exist.CondA T f B G) (hB : DiffVI.Exist.CondB T B) (ηG : ℝ) (hD : CondD T B G ηG)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ)) (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ))
    (hC' : CondC' F E Ψ) (hΨ0 : Ψ 0 = 0) (hE : CondE K E) :
    ∃ ω : ℝ, 0 < ω ∧ ∃ N1 : ℕ, 1 ≤ N1 ∧
      ∀ x0 : EuclideanSpace ℝ (Fin n), ∀ N : ℕ, N1 ≤ N →
        ∀ (xs : ℕ → EuclideanSpace ℝ (Fin n)) (us : ℕ → EuclideanSpace ℝ (Fin m)), DiffVI.Conv.IsScheme K f B G F T θ x0 N xs us →
          us 0 ∈ viSol (fun v => G 0 x0 + F v) K →
          ∀ i < N, ‖us (i + 1)‖ ≤ ω * (1 + ‖xs i‖ + (T / N) * ‖xs (i + 1) - xs i‖) := by sorry

end DiffVI.Cone
