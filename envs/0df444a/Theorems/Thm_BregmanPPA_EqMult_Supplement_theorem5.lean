-- Prove2me | Theorems.Thm_BregmanPPA_EqMult_Supplement_theorem5
-- name    : BregmanPPA.EqMult.Supplement.theorem5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:22:03.814816+00:00
-- url     : https://prove2.me/theorems/9d523893-4d22-46a7-b4f2-c0359e354e91
-- title:
--   Theorem 5 (corrected: alternative (ii) refuted) — convergence, existence under (i), and unboundedness
-- statement:
--   Let $X\subseteq\mathbb R^n$ be closed and convex, let $f:\mathbb R^n\to(-\infty,+\infty]$ be convex and lower semicontinuous with a finite point in $X$, and let $h$ be a Bregman function with zone $S$ containing $\operatorname{ri}F$, where $F=(\operatorname{dom}f)\cap X$. Let $c_k>0$ have a common strictly positive lower bound. A run is a zone-valued sequence satisfying recursion (6),
--
--   $$x^{k+1}\in\operatorname*{argmin}_{z\in X}\{f(z)+c_k^{-1}D_h(z,x^k)\}.$$
--
--   The following are the valid conclusions of Theorem 5, together with a counterexample to its remaining clause.
--
--   1. Every such infinite run converges to a minimizer whenever $f$ attains a minimum on $X$.
--   2. Under alternative (i), $\overline F\subseteq S$ and $\nabla h(S)=\mathbb R^n$, a run exists from every $x^0\in S$.
--   3. Under (i), every such infinite run is unbounded if $f$ has no minimizer on $X$.
--   4. The printed alternative (ii) is false as a guarantee of an infinite run in $S$. For
--      $$S=(0,\infty),\quad X=[0,\infty),\quad h(t)=t^2/2,\quad f(t)=t,\quad c_k=1,\quad x^0=1/2,$$
--      every standing assumption and alternative (ii) holds, but no zone-valued run exists: the first minimizer is $0\notin S$. The Lean conclusion explicitly asserts the Bregman, convexity, lower semicontinuity, relative-interior, finiteness, continuity, lower-bound and step hypotheses of this counterexample as well as nonexistence.
--
--   This companion result describes primal D-function minimization alongside the mission's published equality-multiplier goal. The counterexample locates the open-zone gap in the compactness argument on p. 211; no additional zone-containment or essential-smoothness premise is silently imposed.
--
--   **Formalization Note** The published IsEqProgram predicate supplies precisely the primal assumptions and imposes no equality constraint or dual condition. A run is quantified separately in the convergence and divergence clauses, so their existence is not a premise of the existence conclusion. Unbounded means the range is not bounded. The counterexample is on the real line, the $n=1$ source space up to its canonical isometry. Every dimension of the general conclusions remains allowed.
--
--   Differences from the source:
--   - correction: alternative (ii) guarantees an infinite zone-valued run from every start in S → alternative (ii) is refuted by S=(0,∞), X=[0,∞), h(t)=t²/2, f(t)=t, c_k=1, x⁰=1/2, with all its premises asserted; reason: p. 211 attains the minimum in X but never establishes membership in S; the unique first minimizer is 0 outside S; DISPROOF.md and the independent sorry-free boundary check retain the evidence
--   - correction: the final sentence says f does not attain a minimum on h → f has no minimizer on X; reason: problem (5), the first conclusion and the proof on pp. 210–211 all identify X as the minimization set
--   - encoding: ℝⁿ and f:ℝⁿ→(−∞,+∞], with relative interior and positive-infimum steps → EuclideanSpace ℝ (Fin n), EReal with no bottom, intrinsicInterior, and ∃ ε>0, ∀ k, ε≤c_k; reason: these are the same objects and step condition, including n=0; IsEqProgram bundles exactly closed convex X, convex lower semicontinuous never-bottom f and a finite point in X
--   - encoding: recursion (6) uses D_h on its natural domain and an arg min → all iterates lie in S, each successor is a finite minimizer in X, and the objective is top off closure S; reason: the relative-interior condition places every finite feasible point in closure S; properness provides a finite competitor, so no minimizer instance changes; x⁰ is not required to be feasible
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), pp. 210–211, Theorem 5 and its proof, especially the final compactness paragraph on p. 211; DOI 10.1287/moor.18.1.202

import Mathlib
import Definitions.Def_BregmanPPA_EqMult_Supplement_PrimalRun

open BregmanPPA.Convergence InertialFB.IFB Filter Topology

namespace BregmanPPA.EqMult.Supplement

/-- Theorem 5: convergence, existence under (i), divergence under (i), and a concrete
refutation of the printed existence claim (ii). The last printed `on h` is read `on X`.
No premise is added to repair (ii): the explicit counterexample replaces that false clause. -/
theorem theorem5 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EReal)
    (S : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : ℕ → ℝ) (hP : BregmanPPA.EqMult.IsEqProgram X f)
    (hh : IsBregmanFunction S h)
    (hri : intrinsicInterior ℝ (effectiveFeasible X f) ⊆ S)
    (hc : ∀ k, 0 < c k) (hcinf : ∃ ε > 0, ∀ k, ε ≤ c k) :
    (∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsPrimalRun S X h f c x →
      (∃ z, IsMinimizer X f z) →
      ∃ z, IsMinimizer X f z ∧ Tendsto x atTop (𝓝 z)) ∧
    (AlternativeI S X h f → ∀ x₀ ∈ S,
      ∃ x : ℕ → EuclideanSpace ℝ (Fin n), x 0 = x₀ ∧ IsPrimalRun S X h f c x) ∧
    (∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsPrimalRun S X h f c x →
      AlternativeI S X h f → (¬ ∃ z, IsMinimizer X f z) →
      ¬ Bornology.IsBounded (Set.range x)) ∧
    (IsBregmanFunction (Set.Ioi (0 : ℝ)) (fun t : ℝ => t ^ 2 / 2) ∧
      IsProperFn (fun t : ℝ => (t : EReal)) ∧
      IsConvexFn (fun t : ℝ => (t : EReal)) ∧
      LowerSemicontinuous (fun t : ℝ => (t : EReal)) ∧
      IsClosed (Set.Ici (0 : ℝ)) ∧ Convex ℝ (Set.Ici (0 : ℝ)) ∧
      (∃ z ∈ Set.Ici (0 : ℝ), (z : EReal) ≠ ⊤) ∧
      intrinsicInterior ℝ (effectiveFeasible (Set.Ici (0 : ℝ)) (fun t : ℝ => (t : EReal))) ⊆
        Set.Ioi (0 : ℝ) ∧
      AlternativeII (Set.Ici (0 : ℝ)) (fun t : ℝ => (t : EReal)) ∧
      (∀ k : ℕ, 0 < (fun _ : ℕ => (1 : ℝ)) k) ∧
      (∃ ε > 0, ∀ k : ℕ, ε ≤ (fun _ : ℕ => (1 : ℝ)) k) ∧
      (1 / 2 : ℝ) ∈ Set.Ioi (0 : ℝ) ∧
      ¬ ∃ x : ℕ → ℝ, x 0 = 1 / 2 ∧
        IsPrimalRun (Set.Ioi 0) (Set.Ici 0) (fun t : ℝ => t ^ 2 / 2)
          (fun t : ℝ => (t : EReal)) (fun _ => 1) x) := by sorry

end BregmanPPA.EqMult.Supplement
