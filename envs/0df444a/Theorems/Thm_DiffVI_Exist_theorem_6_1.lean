-- Prove2me | Theorems.Thm_DiffVI_Exist_theorem_6_1
-- name    : DiffVI.Exist.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:23.792821+00:00
-- url     : https://prove2.me/theorems/a1f8f2ea-a7d0-4392-b517-702c765864a5
-- title:
--   Theorem 6.1, p. 40 — under any one of five conditions on (K, F), the initial-value DVI (6.2) with (A), (B) has a weak solution on [0, T] for every x⁰
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a nonempty closed convex set, $T>0$, and let $f:\Omega\to\mathbb R^n$, $B:\Omega\to\mathbb R^{n\times m}$, $G:\Omega\to\mathbb R^m$ on $\Omega=[0,T]\times\mathbb R^n$ satisfy (A) (Lipschitz continuity on $\Omega$) and (B) ($B$ bounded on $\Omega$). Let $F:\mathbb R^m\to\mathbb R^m$. Suppose one of the following holds:
--   1. (a) $F$ is continuous and monotone (on $K$), and some $u^{\mathrm{ref}}\in K$ satisfies the coercivity (6.6);
--   2. (b) $F=E^T\circ\Psi\circ E$ for a matrix $E\in\mathbb R^{\ell\times m}$ with $K_\infty\cap\ker E=\{0\}$ and a continuous $\Psi:\mathbb R^\ell\to\mathbb R^\ell$ strongly monotone on $EK$;
--   3. (c) $0\in K$ and $F(u)=Du$ for a positive semidefinite $D$ such that $(K,D)$ is an R₀ pair;
--   4. (d) $K$ is a polyhedron containing $0$, $F(u)=Du$ for a positive semidefinite $D$, and $G(\Omega)\subseteq\operatorname{int}\mathcal K(K,D)^*$;
--   5. (e) $K$ is a polyhedron containing either the origin or no lines, and $F=D+\Phi$ with $D$ psd-plus, $(K,D)$ an R₀ pair, and $\Phi$ continuous satisfying (6.10) (with $L_\Phi\in(0,1/\rho)$ for some $\rho>0$ for which (6.8) holds) and (6.12) (with $L'_\Phi\in(0,1/L_V)$ for some $L_V>0$ for which (6.9) holds).
--
--   Then for every $x^0\in\mathbb R^n$ the initial-value DVI
--   $$\dot x=f(t,x)+B(t,x)u,\quad x(0)=x^0,\qquad u\in\mathrm{SOL}(K,G(t,x)+F(\cdot))\qquad(6.2)$$
--   has a weak solution $(x,u)$ on $[0,T]$ in the sense of Carathéodory.
--
--   This is the paper's main existence result for DVIs whose ODE is affine in the algebraic variable and whose VI is separable in it; the five conditions describe different classes of DVIs.
--
--   **Formalization Note** "Monotone" in (a) is monotonicity on $K$. (6.6) is stated in the equivalent $\exists c,R$ form. The weak solution includes integrability of the integrands of the integral equation and of (2.4), and (2.4) is required for every continuous $\tilde u:[0,T]\to K$.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 40, Theorem 6.1, (6.2), (A), (B), (6.6), (6.10), (6.12)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Theorem 6.1, p. 40: `K` nonempty closed convex, `(f, B, G)` satisfying (A) and (B). Under any
one of the conditions (a)–(e) on `(K, F)`, the initial-value DVI (6.2) has a weak solution on
`[0, T]` for every initial state `x⁰`. -/
theorem theorem_6_1 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : CondA T f B G) (hB : CondB T B)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hcase :
      -- (a) F continuous and monotone, and (6.6) holds for some u^ref ∈ K
      (Continuous F ∧ IsMonotoneOn F K ∧ ∃ uref ∈ K, Coercive66 K F uref) ∨
      -- (b) F = Eᵀ ∘ Ψ ∘ E, K∞ ∩ ker E = {0}, Ψ continuous and strongly monotone on EK
      (∃ (ℓ : ℕ) (E : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin ℓ))
          (Ψ : EuclideanSpace ℝ (Fin ℓ) → EuclideanSpace ℝ (Fin ℓ)) (η : ℝ),
        (∀ u, F u = (E†) (Ψ (E u))) ∧ recCone K ∩ {v | E v = 0} = {0} ∧
        Continuous Ψ ∧ IsStronglyMonotoneOn Ψ (E '' K) η) ∨
      -- (c) 0 ∈ K, F(u) = Du with D psd and (K, D) an R₀ pair
      ((0 : EuclideanSpace ℝ (Fin m)) ∈ K ∧
        ∃ D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
          (∀ u, F u = D u) ∧ IsPSD D ∧ IsR0Pair K D) ∨
      -- (d) K a polyhedron containing 0, F(u) = Du with D psd, G(Ω) ⊆ int 𝒦(K, D)*
      (IsPolyhedron K ∧ (0 : EuclideanSpace ℝ (Fin m)) ∈ K ∧
        ∃ D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
          (∀ u, F u = D u) ∧ IsPSD D ∧ GOmega T G ⊆ interior (dualCone (viKernel K D))) ∨
      -- (e) K a polyhedron containing 0 or no lines, F = D + Φ with D psd-plus, (K, D) R₀,
      --     Φ continuous with (6.10) and (6.12)
      (IsPolyhedron K ∧ ((0 : EuclideanSpace ℝ (Fin m)) ∈ K ∨ ContainsNoLines K) ∧
        ∃ (D : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
          (Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
          (∀ u, F u = D u + Φ u) ∧ IsPSDPlus D ∧ IsR0Pair K D ∧ Continuous Φ ∧
          -- (6.10): ‖Φ(u)‖ ≤ L_Φ ‖u‖ on K, L_Φ ∈ (0, 1/ρ), ρ > 0 as in (6.8)
          (∃ ρ : ℝ, 0 < ρ ∧
            (∀ r : EuclideanSpace ℝ (Fin m),
              (SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K).Nonempty ∧
              ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + D v) K,
                ‖u‖ ≤ ρ * (1 + ‖r‖)) ∧
            ∃ LΦ : ℝ, 0 < LΦ ∧ LΦ < 1 / ρ ∧ ∀ u ∈ K, ‖Φ u‖ ≤ LΦ * ‖u‖) ∧
          -- (6.12): ‖Φ(u) − Φ(u')‖ ≤ L'_Φ ‖Du − Du'‖ on K, L'_Φ ∈ (0, 1/L_V), L_V > 0 as in (6.9)
          (∃ LV : ℝ, 0 < LV ∧
            (∀ r1 r2 : EuclideanSpace ℝ (Fin m),
              ∀ u1 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r1 + D v) K,
              ∀ u2 ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r2 + D v) K,
                ‖D u1 - D u2‖ ≤ LV * ‖r1 - r2‖) ∧
            ∃ LΦ' : ℝ, 0 < LΦ' ∧ LΦ' < 1 / LV ∧
              ∀ u ∈ K, ∀ u' ∈ K, ‖Φ u - Φ u'‖ ≤ LΦ' * ‖D u - D u'‖))) :
    ∀ x0 : EuclideanSpace ℝ (Fin n), ∃ (x : ℝ → EuclideanSpace ℝ (Fin n))
      (u : ℝ → EuclideanSpace ℝ (Fin m)), IsWeakSolution K f B G F T x0 x u := by sorry

end DiffVI.Exist
