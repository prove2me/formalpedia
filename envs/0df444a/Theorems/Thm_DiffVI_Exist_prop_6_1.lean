-- Prove2me | Theorems.Thm_DiffVI_Exist_prop_6_1
-- name    : DiffVI.Exist.prop_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:23.685955+00:00
-- url     : https://prove2.me/theorems/e16d73e2-0b4e-4cdc-96d4-75a10cc41832
-- title:
--   Proposition 6.1, p. 31 — a weak solution of the DI ẋ ∈ 𝐅(t, x) gives a weak solution (x, u) of the initial-value DVI (6.2)
-- statement:
--   Let $K\subseteq\mathbb R^m$ be nonempty, closed and convex, let $(f,B,G)$ satisfy (A) and (B) on $\Omega=[0,T]\times\mathbb R^n$, $T>0$, let $F:\mathbb R^m\to\mathbb R^m$ be continuous, and suppose that for some $\rho>0$ the linear growth (6.5) holds for all $q\in G(\Omega)$:
--   $$\|u\|\le\rho(1+\|q\|)\qquad\forall q\in G(\Omega),\ u\in\mathrm{SOL}(K,q+F).$$
--   If $x$ is a weak solution in the sense of Carathéodory on $[0,T]$ of the differential inclusion $\dot x\in\mathbf F(t,x)$, $x(0)=x^0$, where $\mathbf F$ is given by (6.4), then there is $u$ such that $(x,u)$ is a weak solution of the initial-value DVI
--   $$\dot x=f(t,x)+B(t,x)u,\quad x(0)=x^0,\qquad u\in\mathrm{SOL}(K,G(t,x)+F(\cdot)).\qquad(6.2)$$
--
--   This links the differential-inclusion formulation to the DVI: existence for the inclusion yields existence for the DVI.
--
--   **Formalization Note** The page concludes that (6.2) "has a weak solution"; the proof keeps the same state trajectory $x$, and the Lean states that. The weak-solution notion includes integrability of the integrands of the integral equation and of (2.4).
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 31, Proposition 6.1, (6.2), (6.4), (6.5)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Proposition 6.1, p. 31: under (A), (B), continuity of `F` and (6.5) on `G(Ω)`, every weak
solution `x` of the DI `ẋ ∈ 𝐅(t, x)`, `x(0) = x⁰` (with `𝐅` from (6.4)) is the state of a weak
solution `(x, u)` of the initial-value DVI (6.2). -/
theorem prop_6_1 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K) (T : ℝ) (hT : 0 < T)
    (f : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (B : ℝ → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (G : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hA : CondA T f B G) (hB : CondB T B)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hFc : Continuous F)
    (ρ : ℝ) (hρ : 0 < ρ) (hlin : LinGrowthSOL K G F T ρ)
    (x0 : EuclideanSpace ℝ (Fin n)) (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx : IsDIWeakSolution T (bigF K f B G F) x0 x) :
    ∃ u : ℝ → EuclideanSpace ℝ (Fin m), IsWeakSolution K f B G F T x0 x u := by sorry

end DiffVI.Exist
