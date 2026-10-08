-- Prove2me | Theorems.Thm_DiffVI_Exist_prop_6_2
-- name    : DiffVI.Exist.prop_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:27:55.762629+00:00
-- url     : https://prove2.me/theorems/c1595173-038f-4b43-a410-0dec2297f759
-- title:
--   Proposition 6.2, p. 32 — under the coercivity (6.6), SOL(K, r + F) ≠ ∅ with linear growth (6.5) for all r, and convex if F is monotone
-- statement:
--   Let $K\subseteq\mathbb R^m$ be a nonempty closed convex set and $F:\mathbb R^m\to\mathbb R^m$ continuous. Suppose there is $u^{\mathrm{ref}}\in K$ with
--   $$\liminf_{u\in K,\ \|u\|\to\infty}\frac{(u-u^{\mathrm{ref}})^TF(u)}{\|u\|^2}>0.\qquad(6.6)$$
--   Then:
--   1. for every $r\in\mathbb R^m$, $\mathrm{SOL}(K,r+F)\neq\emptyset$;
--   2. there is $\rho>0$ such that $\|u\|\le\rho(1+\|r\|)$ for all $r\in\mathbb R^m$ and all $u\in\mathrm{SOL}(K,r+F)$;
--   3. if $F$ is monotone on $K$, then $\mathrm{SOL}(K,r+F)$ is convex for every $r$.
--
--   This gives the hypotheses of Lemma 6.2 and the convexity needed by Lemma 6.1 in case (a) of Theorem 6.1.
--
--   **Formalization Note** (6.6) is stated in the equivalent form "there are $c>0$ and $R$ with $(u-u^{\mathrm{ref}})^TF(u)\ge c\|u\|^2$ for $u\in K$, $\|u\|\ge R$". The page says "if $F$ is monotone" without a set; the Lean assumes monotonicity on $K$, which is what the convexity argument uses and is the weaker hypothesis.
-- source:
--   Pang & Stewart, Differential variational inequalities, author's version hal-01366027v1, p. 32, Proposition 6.2, (6.5), (6.6)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol
import Definitions.Def_DiffVI_Exist_Setting

open MeasureTheory
open scoped InnerProductSpace InnerProduct

namespace DiffVI.Exist

/-- Proposition 6.2, p. 32: under the coercivity (6.6), `SOL(K, r + F)` is nonempty for every
`r ∈ ℝᵐ`, the linear growth (6.5) holds for all `r ∈ ℝᵐ`, and `SOL(K, r + F)` is convex when `F`
is monotone (on `K`). -/
theorem prop_6_2 {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m))) (hKne : K.Nonempty)
    (hKcl : IsClosed K) (hKcv : Convex ℝ K)
    (F : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (hFc : Continuous F)
    (uref : EuclideanSpace ℝ (Fin m)) (huref : uref ∈ K) (hcoer : Coercive66 K F uref) :
    (∀ r : EuclideanSpace ℝ (Fin m),
      (SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K).Nonempty) ∧
    (∃ ρ : ℝ, 0 < ρ ∧ ∀ r : EuclideanSpace ℝ (Fin m),
      ∀ u ∈ SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K, ‖u‖ ≤ ρ * (1 + ‖r‖)) ∧
    (IsMonotoneOn F K → ∀ r : EuclideanSpace ℝ (Fin m),
      Convex ℝ (SolodovSvaiterVI.Alg21.viSol (fun v => r + F v) K)) := by sorry

end DiffVI.Exist
