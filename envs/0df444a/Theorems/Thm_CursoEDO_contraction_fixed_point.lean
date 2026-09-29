-- Prove2me | Theorems.Thm_CursoEDO_contraction_fixed_point
-- name    : CursoEDO.contraction_fixed_point
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T15:18:44.112829+00:00
-- url     : https://prove2.me/theorems/4a49c22a-178a-4b7a-bbc6-b2c6ab708e75
-- title:
--   Teorema 0.2.10 — Banach fixed point theorem for contractions
-- statement:
--   **Banach fixed point theorem for contractions.**
--
--   Let $(X,d)$ be a nonempty complete metric space and let $F : X \to X$ be a contraction: there is a
--   constant $\lambda$ with $0 \le \lambda < 1$ such that
--
--   $$
--   d\bigl(F(x), F(y)\bigr) \;\le\; \lambda\, d(x,y) \qquad \text{for all } x, y \in X .
--   $$
--
--   Then $F$ has a fixed point $p$, it is the only one, and it attracts every orbit: for every
--   $x \in X$ the sequence of iterates $F^n(x)$ converges to $p$ as $n \to \infty$, where $F^n$ is
--   defined inductively by $F^n(x) = F(F^{n-1}(x))$.
--
--   This is Teorema 0.2.10 of the source (p. 10). In the *Curso de EDO* development it is the tool
--   that produces the solution of the Cauchy problem: the Picard operator, or one of its iterates, is
--   shown to be a contraction on a complete space of continuous functions, and its unique fixed point
--   is the solution. It is used again later in the book for the perturbation-of-the-identity theorem
--   and in the proofs of Grobman–Hartman and of the stable manifold theorem.
-- source:
--   Augusto Armando de Castro Junior, Curso de Equacoes Diferenciais Ordinarias, lecture notes, 06 January 2009, p. 10, Teorema 0.2.10 (Ponto fixo para contracoes)

import Mathlib

namespace CursoEDO
theorem contraction_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (F : X → X) (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam < 1)
    (hF : ∀ x y : X, dist (F x) (F y) ≤ lam * dist x y) :
    ∃ p : X, F p = p ∧ (∀ q : X, F q = q → q = p) ∧
      ∀ x : X, Filter.Tendsto (fun n : ℕ => F^[n] x) Filter.atTop (nhds p) := by sorry
end CursoEDO
