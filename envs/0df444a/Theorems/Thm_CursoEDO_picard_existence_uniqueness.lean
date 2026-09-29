-- Prove2me | Theorems.Thm_CursoEDO_picard_existence_uniqueness
-- name    : CursoEDO.picard_existence_uniqueness
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T15:23:04.219731+00:00
-- url     : https://prove2.me/theorems/58cbdc7f-051d-4bfe-ba82-84ff6cfb8949
-- title:
--   Teorema 2.1.2 (Picard) — local existence and uniqueness in a Banach space
-- statement:
--   **Picard's local existence and uniqueness theorem in a Banach space.**
--
--   Let $E$ be a real Banach space, $t_0 \in \mathbb R$, $x_0 \in E$, and $a, b > 0$. Consider the
--   "box"
--
--   $$
--   U \;=\; [t_0-a,\ t_0+a] \times \bar B(x_0,b), \qquad
--   \bar B(x_0,b) = \{x \in E : \|x-x_0\| \le b\},
--   $$
--
--   and a map $f$ assigning $f(t,x)\in E$ to $(t,x) \in U$ which is
--
--   1. continuous on $U$;
--   2. bounded on $U$, with $M$ the least upper bound of $\{\|f(t,x)\| : (t,x) \in U\}$ and $M>0$;
--   3. Lipschitz with respect to the second variable on $U$ with a constant $c>0$, i.e.
--      $\|f(t,x_1)-f(t,x_2)\| \le c\,\|x_1-x_2\|$ for all $(t,x_1),(t,x_2)\in U$.
--
--   Set
--
--   $$
--   \alpha \;=\; \min\left\{\,a,\ \frac{b}{M}\,\right\}.
--   $$
--
--   Then the Cauchy problem
--
--   $$
--   \frac{dx}{dt} = f(t,x), \qquad x(t_0) = x_0
--   $$
--
--   has a solution $\varphi$ on $[t_0-\alpha,\ t_0+\alpha]$ whose graph stays in $U$, and that
--   solution is unique: any solution $\psi$ on the same interval whose graph stays in $U$ satisfies
--   $\varphi(t)=\psi(t)$ for every $t \in [t_0-\alpha,\ t_0+\alpha]$. At the two endpoints the
--   differential equation is understood with the corresponding one-sided derivative.
--
--   This is Teorema 2.1.2 (Picard) of the source (p. 44), the goal of this mission. It is the result
--   that makes the initial value problem well posed and thereby licenses the notions of trajectory and
--   flow used throughout the rest of the book; in finite dimension the boundedness hypothesis is
--   automatic on the compact box and may be dropped.
--
--   **Formalization Note.** $M$ is required to be a least upper bound of the set of values
--   $\|f(t,x)\|$ on $U$, which simultaneously expresses the boundedness hypothesis and the definition
--   of $M$; the hypothesis $M>0$ is stated explicitly so that $b/M$ is meaningful. Uniqueness is
--   asserted as agreement of the two solutions on $[t_0-\alpha, t_0+\alpha]$, since solutions are
--   modelled as total functions whose values outside the interval are unconstrained.
-- source:
--   Augusto Armando de Castro Junior, Curso de Equacoes Diferenciais Ordinarias, lecture notes, 06 January 2009, p. 44, Teorema 2.1.2 (Picard)

import Mathlib
import Definitions.Def_CursoEDO_Defs

namespace CursoEDO
theorem picard_existence_uniqueness {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (t₀ : ℝ) (x₀ : E) (a b M α : ℝ) (c : ℝ) (f : ℝ → E → E)
    (U : Set (ℝ × E))
    (ha : 0 < a) (hb : 0 < b)
    (hU : U = Set.Icc (t₀ - a) (t₀ + a) ×ˢ Metric.closedBall x₀ b)
    (hcont : ContinuousOn (fun p : ℝ × E => f p.1 p.2) U)
    (hM : IsLUB {r : ℝ | ∃ p ∈ U, r = ‖f p.1 p.2‖} M) (hM0 : 0 < M)
    (hlip : LipschitzInSecondVar U (fun p : ℝ × E => f p.1 p.2) c)
    (hα : α = min a (b / M)) :
    ∃ φ : ℝ → E, IsCauchySolutionOn f U t₀ x₀ (Set.Icc (t₀ - α) (t₀ + α)) φ ∧
      ∀ ψ : ℝ → E, IsCauchySolutionOn f U t₀ x₀ (Set.Icc (t₀ - α) (t₀ + α)) ψ →
        Set.EqOn φ ψ (Set.Icc (t₀ - α) (t₀ + α)) := by sorry
end CursoEDO
