-- Prove2me | Theorems.Thm_CompositeSAA_stability_of_beta0_convergence
-- name    : CompositeSAA.stability_of_beta0_convergence
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:36:07.781964+00:00
-- url     : https://prove2.me/theorems/120630b6-6a79-495e-900d-9d4a64735cbb
-- title:
--   Theorem 3 — stability of the composite problem under $\beta_0$-convergent perturbations (corrected: nonempty perturbed solution sets, $\bar f^P$ continuous)
-- statement:
--   Assume the standing assumptions on problem (3), with compact sets $\mathcal U$, $I_1,\dots,I_k$. Let $Q^j_N$ ($j=1,\dots,k+1$, $N\in\mathbb N$) be measures such that $\beta_0(Q^j_N,P)\to0$ for every $j$, i.e.
--
--   $$
--   \sup_{(u,\eta)\in\mathcal U\times I_j}\bigl\|\bar f^{Q^j_N}_j(u,\eta)-\bar f^P_j(u,\eta)\bigr\|\to0\ (j\le k),\qquad \sup_{u\in\mathcal U}\bigl\|\bar f^{Q^{k+1}_N}_{k+1}(u)-\bar f^P_{k+1}(u)\bigr\|\to0 .
--   $$
--
--   Assume that $\bar f^P_j$ is continuous on $\mathcal U\times I_j$ and $\bar f^P_{k+1}$ on $\mathcal U$, and that for all $N$ large enough the perturbed problem (8) has a nonempty solution set $S^{(Q_N)}\subseteq\mathcal U$ (Assumption 2). Then
--
--   1. $\varrho^{(Q^1_N..Q^{k+1}_N)}[u,X]\to\varrho[u,X]$ for every $u\in\mathcal U$;
--   2. $\vartheta^{(Q^1_N..Q^{k+1}_N)}\to\vartheta$;
--   3. $\mathsf d(S^{(Q^1_N..Q^{k+1}_N)},S)\to0$;
--   4. if problem (3) has a unique solution $\hat u$, then $\mathsf D(S^{(Q^1_N..Q^{k+1}_N)},S)\to0$.
--
--   This is the deterministic stability theorem on which all the sample-based results of the paper rest.
--
--   Differences from the source:
--   - correction: Assumption 2, "$S^{(Q_N)}\subset\mathcal U$ for $N$ large enough" → "$S^{(Q_N)}\ne\emptyset$ and $S^{(Q_N)}\subseteq\mathcal U$ for $N$ large enough"; reason: as printed it holds vacuously when the perturbed problem has no minimizer, and the theorem is false: with $f_1(u,\eta,x)=u^2/(1+u^2)+ux$, $f_2=0$, $U=\mathbb R$, $\mathcal U=I_1=[-1,1]$, $P=\delta_0$, $Q^j_N=\delta_{1/N}$, one has $\beta_0(Q^j_N,P)\le1/N$, but $\varrho_N(u)=u^2/(1+u^2)+u/N$ has no minimum, so $S_N=\emptyset\subset\mathcal U$ while $\vartheta_N\not\to\vartheta=0$.
--   - correction: added "$\bar f^P_j$ continuous on $\mathcal U\times I_j$ and $\bar f^P_{k+1}$ on $\mathcal U$"; reason: the proof places $\bar f^P$ in the space $\mathcal H$ of continuous functions, which the printed hypotheses do not imply; with $U=\mathcal U=I_1=[0,1]$, $P$ uniform on $[0,1]$, $f_2(u,x)=x$, $f_1(u,\eta,x)=u^2+T(\eta,x)$ for a unit-mass tent $T(\eta,\cdot)$ on $[0,2(\eta-\tfrac12)]$ ($T=0$ for $\eta\le\tfrac12$), and $Q^1_N=P$, $Q^2_N=(1-\tfrac1N)P+\tfrac1N\delta_1$, one has $\beta_0(Q^j_N,P)\le1/N$ and $S_N=\{0\}$, yet $\vartheta_N=1\not\to\vartheta=0$.
--   - encoding: the printed "Assumption 1" → Assumption 2 of p.6; reason: label slip in the cross-reference.
--   - generalization: $\beta_0(Q^j_N,P)\to0$, a supremum over all of $\mathfrak F_0$ (every level's functions) → uniform convergence on $\mathcal U\times I_j$ of the level-$j$ integrals only ($f_j(u,\eta,\cdot)$ against $Q^j_N$; $f_{k+1}(u,\cdot)$ on $\mathcal U$ against $Q^{k+1}_N$), in $\varepsilon$-eventually form; reason: the proof uses only the uniform convergence of each level map, and the printed hypothesis implies this one; the $\varepsilon$-form avoids a real supremum over a possibly unbounded family.
--   - generalization: $Q^j_N\in\mathcal P(\mathcal X)$ → arbitrary measures on $\mathbb R^m$, with integrals over $\mathbb R^m$; reason: the proof uses only the uniform convergence of the level integrals, and for $Q\in\mathcal P(\mathcal X)$ the integrals over $\mathcal X$ and over $\mathbb R^m$ coincide.
--   - generalization: "without loss of generality $\mathcal U$ and $I_j$ are convex" (p.5) → not assumed; reason: the statement does not use convexity, and convex sets are an instance.
--   - encoding: $\mathbb R^d$ as `EuclideanSpace ℝ (Fin d)` with a dimension family $m_0=1$; $\mathsf d$ and $\mathsf D$ in $[0,\infty]$; $S$ as the set of minimizers and $\vartheta$ as an infimum that is attained under the hypotheses; reason: Lean convention, same instances.
-- source:
--   Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 3, p.6 (with Assumption 2, p.6)

import Mathlib
import Definitions.Def_CompositeSAA_CompositeModel
import Definitions.Def_CompositeSAA_perturbedObjective
import Definitions.Def_CompositeSAA_riskFunctional
import Definitions.Def_CompositeSAA_optimalValue
import Definitions.Def_CompositeSAA_solutionSet
import Definitions.Def_CompositeSAA_excess
import Definitions.Def_CompositeSAA_StandingAssumptions

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CompositeSAA

/-- Dentcheva, Lin, Penev, arXiv:2201.01338v1, Theorem 3, p.6 (corrected): stability of the
composite problem under measure perturbations that converge in the metric `β₀`.

Under the standing assumptions, let `Q^j_N` (`j = 1, …, k + 1`) be measures with
`β₀(Q^j_N, P) → 0`, i.e. `f̄^{Q^j_N}_j → f̄^P_j` uniformly on `𝒰 × I_j` (and
`f̄^{Q^{k+1}_N}_{k+1} → f̄^P_{k+1}` uniformly on `𝒰`). Assume `f̄^P_j` is continuous on `𝒰 × I_j`
and `f̄^P_{k+1}` on `𝒰`, and Assumption 2 with nonemptiness: for `N` large,
`S^{(Q_N)} ≠ ∅` and `S^{(Q_N)} ⊆ 𝒰`. Then `ϱ^{(Q_N)}[u] → ϱ[u]` for every `u ∈ 𝒰`,
`ϑ^{(Q_N)} → ϑ`, `d(S^{(Q_N)}, S) → 0`, and if `S = {û}` then `D(S^{(Q_N)}, S) → 0`.

**Formalization Note**
1. `Q N j` is `Q^j_N`. `β₀(Q^j_N, P) → 0` is written in `ε`-eventually form, avoiding a real
   supremum, and only for the functions of level `j` (`f_j(u, η, ·)`, `(u, η) ∈ 𝒰 × I_j`, resp.
   `f_{k+1}(u, ·)`, `u ∈ 𝒰`) integrated against `Q^j_N`; the paper's `β₀` takes the supremum over
   all of `𝔉₀` (p.5), so this hypothesis is weaker than the printed one.
2. Correction (nonemptiness): as printed, Assumption 2 holds vacuously when `S^{(Q_N)} = ∅`, and
   the theorem is then false.
3. Correction (continuity of `f̄^P`): the proof places `f̄^P` in `ℋ`, a space of continuous
   functions; the printed hypotheses do not imply it.
4. The printed "Assumption 1" is Assumption 2 (p.6). -/
theorem stability_of_beta0_convergence {n mX k : ℕ} (D : CompositeModel n mX k)
    (P : Measure (EuclideanSpace ℝ (Fin mX))) (𝒳 : Set (EuclideanSpace ℝ (Fin mX)))
    (U 𝒰 : Set (EuclideanSpace ℝ (Fin n)))
    (I : (j : ℕ) → Set (EuclideanSpace ℝ (Fin (D.m j))))
    (hstd : StandingAssumptions D P 𝒳 U 𝒰 I)
    (Q : ℕ → ℕ → Measure (EuclideanSpace ℝ (Fin mX)))
    (hβ : ∀ j, 1 ≤ j → j ≤ k → ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ 𝒰, ∀ η ∈ I j,
      ‖∫ x, D.f j u η x ∂(Q N j) - ∫ x, D.f j u η x ∂P‖ ≤ ε)
    (hβLast : ∀ ε > 0, ∀ᶠ N in atTop, ∀ u ∈ 𝒰,
      ‖∫ x, D.fLast u x ∂(Q N (k + 1)) - ∫ x, D.fLast u x ∂P‖ ≤ ε)
    (hcont : ∀ j, 1 ≤ j → j ≤ k →
      ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin (D.m j)) =>
        ∫ x, D.f j p.1 p.2 x ∂P) (𝒰 ×ˢ I j))
    (hcontLast : ContinuousOn (fun u => ∫ x, D.fLast u x ∂P) 𝒰)
    (hA2 : ∀ᶠ N in atTop, (solutionSet (perturbedObjective D (Q N)) U).Nonempty ∧
      solutionSet (perturbedObjective D (Q N)) U ⊆ 𝒰) :
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
