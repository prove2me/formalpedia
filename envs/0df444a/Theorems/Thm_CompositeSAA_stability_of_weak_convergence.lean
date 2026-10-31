-- Prove2me | Theorems.Thm_CompositeSAA_stability_of_weak_convergence
-- name    : CompositeSAA.stability_of_weak_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:36.464001+00:00
-- url     : https://prove2.me/theorems/52ad0aed-15b7-4373-a3dc-25d02e310f7c
-- title:
--   Theorem 4 — stability of the composite problem under weak convergence, cases (a) and (b) (corrected: nonempty perturbed solution sets)
-- statement:
--   Assume the standing assumptions on problem (3). Let $Q^j_N\in\mathcal P(\mathcal X)$ ($j=1,\dots,k+1$) be probability measures concentrated on $\mathcal X$ with $Q^j_N\to P$ weakly as $N\to\infty$, and assume that for all $N$ large enough the perturbed problem (8) has a nonempty solution set $S^{(Q_N)}\subseteq\mathcal U$ (Assumption 2). Suppose one of the following conditions:
--
--   (a) for all $(u,\eta)\in\mathcal U\times I$, every component of $f_j(u,\eta_j,\cdot)$ ($j\le k$) and of $f_{k+1}(u,\cdot)$ belongs to $\mathfrak F$, i.e. is $1$-Lipschitz and bounded by $1$ on $\operatorname{conv}(\mathcal X)$;
--
--   (b) every such component belongs to $\tilde{\mathfrak F}$, i.e. admits the given modulus of continuity on $\operatorname{conv}(\mathcal X)$ uniformly in $(u,\eta)\in\mathcal U\times I$, and
--
--   $$
--   \lim_{N\to\infty}\int\|x\|\,Q^j_N(dx)=\int\|x\|\,P(dx),\qquad j=1,\dots,k+1,
--   $$
--
--   with all integrals finite.
--
--   Then the conclusions of Theorem 3 hold: $\varrho^{(Q_N)}[u,X]\to\varrho[u,X]$ for every $u\in\mathcal U$, $\vartheta^{(Q_N)}\to\vartheta$, $\mathsf d(S^{(Q_N)},S)\to0$, and if problem (3) has a unique solution $\hat u$ then $\mathsf D(S^{(Q_N)},S)\to0$.
--
--   Case (b) is what the smoothed estimators need: kernel-smoothed empirical measures converge weakly with their first moments, but the composite functions are typically unbounded.
--
--   Differences from the source:
--   - correction: Assumption 2 → with "$S^{(Q_N)}\ne\emptyset$" added; reason: as printed it holds vacuously on an empty solution set and the theorem is false: with $f_1(u,\eta,x)=u^2/(1+u^2)+ux$, $f_2=0$, $U=\mathbb R$, $\mathcal U=I_1=[-1,1]$, $P=\delta_0$, $Q^j_N=\delta_{1/N}$, case (b) holds with $w(t)=t$, yet $\varrho_N$ has no minimum and $\vartheta_N\not\to0$.
--   - encoding: the printed "Assumption 1" → Assumption 2 of p.6; reason: label slip in the cross-reference.
--   - reading: "for all $(u,\eta)\in U\times I$" in (a) → $(u,\eta)\in\mathcal U\times I$; reason: the classes $\mathfrak F_0$ and $\tilde{\mathfrak F}$ range over $\mathcal U$ (p.5), and the $\mathcal U$ reading is the weaker hypothesis.
--   - encoding: membership of the vector functions in $\mathfrak F$, $\tilde{\mathfrak F}$ → componentwise, with one modulus per component (the paper's $w_\ell$, $\ell=1,\dots,d$, indexed by level and component); reason: same instances.
--   - generalization: weak convergence in $\mathcal P(\mathcal X)$ → weak convergence of the measures on $\mathbb R^m$ (bounded continuous test functions on $\mathbb R^m$); reason: the former implies the latter.
--   - generalization: "without loss of generality $\mathcal U$ and $I_j$ are convex" → not assumed; reason: convex sets are an instance.
--   - encoding: $\mathbb R^d$, $\mathsf d$, $\mathsf D$, $S$, $\vartheta$ as in Theorem 3; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 4, p.7 (with Assumption 2, p.6, and the classes 𝔉, 𝔉̃ of p.5)

import Mathlib
import Definitions.Def_CompositeSAA_CompositeModel
import Definitions.Def_CompositeSAA_perturbedObjective
import Definitions.Def_CompositeSAA_riskFunctional
import Definitions.Def_CompositeSAA_optimalValue
import Definitions.Def_CompositeSAA_solutionSet
import Definitions.Def_CompositeSAA_excess
import Definitions.Def_CompositeSAA_StandingAssumptions
import Definitions.Def_CompositeSAA_IsModulus

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 4, p.7 (corrected): stability of the
composite problem under weak convergence of the level measures.

Under the standing assumptions, let `Q^j_N ∈ 𝒫(𝒳)` (`j = 1, …, k + 1`) converge weakly to `P`,
and let Assumption 2 hold with nonemptiness. Suppose one of:

(a) every component of `f_j(u, η_j, ·)` and of `f_{k+1}(u, ·)` belongs to `𝔉`, i.e. is
    `1`-Lipschitz and bounded by `1` on `conv(𝒳)`, for all `(u, η) ∈ 𝒰 × I`;
(b) every component belongs to `𝔉̃`, i.e. admits the given modulus of continuity on `conv(𝒳)`
    uniformly in `(u, η) ∈ 𝒰 × I`, and `∫ ‖x‖ dQ^j_N → ∫ ‖x‖ dP`, all integrals finite.

Then the conclusions of Theorem 3 hold: `ϱ^{(Q_N)}[u] → ϱ[u]` for every `u ∈ 𝒰`,
`ϑ^{(Q_N)} → ϑ`, `d(S^{(Q_N)}, S) → 0`, and if `S = {û}` then `D(S^{(Q_N)}, S) → 0`.

**Formalization Note**
1. `Q N j` is `Q^j_N`; `conv(𝒳)` is the closed convex hull. Weak convergence is written with
   bounded continuous test functions on `ℝ^m`. The moduli of `𝔉̃` are `w j i` for the `i`-th
   component of `f_j` and `wLast i` for `f_{k+1}`; they are used only under (b).
2. Correction: Assumption 2 includes `S^{(Q_N)} ≠ ∅` (as printed it is vacuous on `∅`).
3. The printed "Assumption 1" is Assumption 2; the printed range "`(u, η) ∈ U × I`" in (a) is
   read as `𝒰 × I`, the range over which `𝔉₀` and `𝔉̃` are defined (p.5). -/
theorem stability_of_weak_convergence {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (𝒳 : Set (EuclideanSpace ℝ (Fin mX)))
    (U 𝒰 : Set (EuclideanSpace ℝ (Fin n)))
    (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (D.m j))))
    (hstd : StandingAssumptions D P 𝒳 U 𝒰 I)
    (Q : ℕ → ℕ → Measure (EuclideanSpace ℝ (Fin mX)))
    (hQ : ∀ N j, 1 ≤ j → j ≤ k + 1 → IsProbabilityMeasure (Q N j) ∧ ∀ᵐ x ∂(Q N j), x ∈ 𝒳)
    (hweak : ∀ j, 1 ≤ j → j ≤ k + 1 → ∀ g : EuclideanSpace ℝ (Fin mX) →ᵇ ℝ,
      Tendsto (fun N => ∫ x, g x ∂(Q N j)) atTop (𝓝 (∫ x, g x ∂P)))
    (hA2 : ∀ᶠ N in atTop, (solutionSet (perturbedObjective D (Q N)) U).Nonempty ∧
      solutionSet (perturbedObjective D (Q N)) U ⊆ 𝒰)
    (w : (j : ℕ) → Fin (D.m (j - 1)) → ℝ → ℝ) (wLast : Fin (D.m k) → ℝ → ℝ)
    (hcases :
      ((∀ j, 1 ≤ j → j ≤ k → ∀ u ∈ 𝒰, ∀ η ∈ I j, ∀ i,
          (∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
            |D.f j u η x i - D.f j u η x' i| ≤ ‖x - x'‖) ∧
          ∀ x ∈ closedConvexHull ℝ 𝒳, |D.f j u η x i| ≤ 1) ∧
        (∀ u ∈ 𝒰, ∀ i,
          (∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
            |D.fLast u x i - D.fLast u x' i| ≤ ‖x - x'‖) ∧
          ∀ x ∈ closedConvexHull ℝ 𝒳, |D.fLast u x i| ≤ 1)) ∨
      ((∀ j, 1 ≤ j → j ≤ k → ∀ i, IsModulus (w j i)) ∧ (∀ i, IsModulus (wLast i)) ∧
        (∀ j, 1 ≤ j → j ≤ k → ∀ u ∈ 𝒰, ∀ η ∈ I j, ∀ i,
          ∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
            |D.f j u η x i - D.f j u η x' i| ≤ w j i ‖x - x'‖) ∧
        (∀ u ∈ 𝒰, ∀ i, ∀ x ∈ closedConvexHull ℝ 𝒳, ∀ x' ∈ closedConvexHull ℝ 𝒳,
            |D.fLast u x i - D.fLast u x' i| ≤ wLast i ‖x - x'‖) ∧
        Integrable (fun x => ‖x‖) P ∧
        (∀ N j, 1 ≤ j → j ≤ k + 1 → Integrable (fun x => ‖x‖) (Q N j)) ∧
        ∀ j, 1 ≤ j → j ≤ k + 1 →
          Tendsto (fun N => ∫ x, ‖x‖ ∂(Q N j)) atTop (𝓝 (∫ x, ‖x‖ ∂P)))) :
    (∀ u ∈ 𝒰, Tendsto (fun N => perturbedObjective D (Q N) u) atTop
        (𝓝 (riskFunctional D P u))) ∧
      Tendsto (fun N => optimalValue (perturbedObjective D (Q N)) U) atTop
        (𝓝 (optimalValue (riskFunctional D P) U)) ∧
      Tendsto (fun N => excess (solutionSet (perturbedObjective D (Q N)) U)
        (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) ∧
      ∀ û, solutionSet (riskFunctional D P) U = {û} →
        Tendsto (fun N => Metric.hausdorffEDist (solutionSet (perturbedObjective D (Q N)) U)
          (solutionSet (riskFunctional D P) U)) atTop (𝓝 0) := by sorry

end CompositeSAA
