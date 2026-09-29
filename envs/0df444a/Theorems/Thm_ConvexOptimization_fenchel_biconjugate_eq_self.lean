-- Prove2me | Theorems.Thm_ConvexOptimization_fenchel_biconjugate_eq_self
-- name    : ConvexOptimization.fenchel_biconjugate_eq_self
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:41:54.871529+00:00
-- url     : https://prove2.me/theorems/26a44ea9-db6c-41a5-bbbe-7908a1598998
-- title:
--   Fenchel–Moreau biconjugation
-- statement:
--   **The Fenchel–Moreau theorem:** a convex function equals its own biconjugate.
--
--   Let $f : \mathbb{R}^n \to \mathbb{R}$ be convex on all of $\mathbb{R}^n$ (and finite-valued), with conjugate $f^{*}(y) = \sup_x(\langle x,y\rangle - f(x))$ and biconjugate $f^{**}(x) = \sup_y(\langle x,y\rangle - f^{*}(y))$. Then
--
--   $$f^{**}(x) \;=\; f(x) \qquad \text{for every } x \in \mathbb{R}^n .$$
--
--   Since $f^{**}$ is by construction the supremum of all affine functions lying below $f$, the theorem says a convex function is exactly the upper envelope of its affine minorants — the analytic counterpart of the statement that a closed convex set is the intersection of the halfspaces containing it, and thus a direct descendant of the separating hyperplane theorem.
--
--   Conjugation is therefore an involution on this class of functions, which is what makes dual descriptions lossless: for a convex problem, dualizing twice returns the original problem, and the duality gap of a nonconvex problem measures precisely the distance from $f$ to $f^{**}$.
--
--   **Formalization Note** Finiteness of $f$ is built into its type `EuclideanSpace ℝ (Fin n) → ℝ`, and convexity is `ConvexOn ℝ Set.univ f`; a finite-valued convex function on all of $\mathbb{R}^n$ is automatically continuous, so no closedness hypothesis is needed. The conclusion equates an `EReal` value with the coercion of a real number, which also asserts finiteness of $f^{**}(x)$. Source: B&V §3.3.2, p. 94.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 94, §3.3.2 (the biconjugate; f** = f for closed convex f)

import Mathlib
import Definitions.Def_fenchelConjugate
import Definitions.Def_fenchelBiconjugate

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.fenchel_biconjugate_eq_self {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ConvexOn ℝ Set.univ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    fenchelBiconjugate f x = (f x : EReal) := by
  sorry
