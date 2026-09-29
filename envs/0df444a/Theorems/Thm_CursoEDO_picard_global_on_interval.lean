-- Prove2me | Theorems.Thm_CursoEDO_picard_global_on_interval
-- name    : CursoEDO.picard_global_on_interval
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T15:22:42.496431+00:00
-- url     : https://prove2.me/theorems/d989c1c2-07a8-4a48-909c-520634cbfe9d
-- title:
--   Corolário 2.1.3 — existence and uniqueness on a whole interval
-- statement:
--   **Existence and uniqueness on the whole interval, for a globally Lipschitz field.**
--
--   Let $E$ be a real Banach space, and let $I \subseteq \mathbb R$ be a nondegenerate interval (that
--   is, convex with nonempty interior). Let $f$ assign $f(t,x) \in E$ to each $(t,x) \in I \times E$,
--   be continuous there, and be Lipschitz with respect to the second variable on $I \times E$ with a
--   constant $c>0$:
--
--   $$
--   \|f(t,x_1) - f(t,x_2)\| \;\le\; c\,\|x_1-x_2\| \qquad \text{for all } t \in I,\ x_1,x_2 \in E .
--   $$
--
--   Fix $t_0 \in I$ and $x_0 \in E$. Then the Cauchy problem $x' = f(t,x)$, $x(t_0)=x_0$ has a
--   solution defined on **all** of $I$, and any two solutions defined on $I$ agree throughout $I$.
--
--   This is Corolário 2.1.3 of the source (p. 46). In contrast with Picard's local theorem, no ball
--   around $x_0$ and no boundedness assumption on $f$ appear: because the Lipschitz condition holds
--   across the whole space $E$, the local solutions can be glued over every compact subinterval of
--   $I$. It is the statement responsible for global existence for linear equations, where
--   $f(t,x)=A(t)x + b(t)$ is Lipschitz in $x$ on each compact time interval, and it is the form used
--   in the book's chapter on linear equations.
-- source:
--   Augusto Armando de Castro Junior, Curso de Equacoes Diferenciais Ordinarias, lecture notes, 06 January 2009, p. 46, Corolario 2.1.3

import Mathlib
import Definitions.Def_CursoEDO_Defs

namespace CursoEDO
theorem picard_global_on_interval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (I : Set ℝ) (hIconv : Convex ℝ I) (hIne : (interior I).Nonempty)
    (t₀ : ℝ) (ht₀ : t₀ ∈ I) (x₀ : E) (f : ℝ → E → E) (c : ℝ)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) (I ×ˢ (Set.univ : Set E)))
    (hlip : LipschitzInSecondVar (I ×ˢ (Set.univ : Set E)) (fun p : ℝ × E => f p.1 p.2) c) :
    ∃ φ : ℝ → E, IsCauchySolutionOn f (I ×ˢ (Set.univ : Set E)) t₀ x₀ I φ ∧
      ∀ ψ : ℝ → E, IsCauchySolutionOn f (I ×ˢ (Set.univ : Set E)) t₀ x₀ I ψ →
        Set.EqOn φ ψ I := by sorry
end CursoEDO
