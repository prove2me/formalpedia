-- Prove2me | Theorems.Thm_ChenWasserstein_Reform_theorem_2
-- name    : ChenWasserstein.Reform.theorem_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:19:16.53567+00:00
-- url     : https://prove2.me/theorems/d39f9d84-d45c-460c-9a8f-75e6a9f883af
-- title:
--   Theorem 2 — fractional sorted-distance feasibility criterion
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel sigma algebra, let $N\ge1$, and let $\xi_1,\ldots,\xi_N\in E$ be arbitrary samples, with repetitions permitted. Let $S\subseteq E$ be open with nonempty complement $C=E\setminus S$. Write $d_i=\inf_{y\in C}\|\xi_i-y\|$, $\widehat P=N^{-1}\sum_i\delta_{\xi_i}$, and $\mathcal F(\theta)=\{P\text{ a Borel probability law}:W_1(\widehat P,P)\le\theta\}$, where $W_1$ is the infimum of the expected norm cost over all couplings. Assume $\theta>0$.
--
--   At a fixed decision, take $S$ to be its safety set and let $0<\varepsilon<1$. Then the robust chance constraint is equivalent to the fractional sorted-distance inequality:
--   $$\sup_{P\in\mathcal F(\theta)}P(C)\le\varepsilon\quad\Longleftrightarrow\quad\frac1N F_d(\varepsilon N)\ge\theta.$$
--   Here $F_d$ sums the smallest $\lfloor\varepsilon N\rfloor$ distances and adds the fractional remainder times the next distance. This criterion permits ties, unsafe samples, nonintegral $\varepsilon N$, and equality at the threshold.
--
--   This is the intermediate feasibility criterion connecting the robust model to a finite array of distances.
--
--   **Formalization Note** The fixed decision is suppressed by using its set $S=S(x)$ directly; no assumptions about the whole decision set or existence of an optimizer enter this pointwise assertion. The nonempty complement is the source's implicit nearest-point convention (F1). The published multiset order statistic replaces an explicit sorting permutation without changing multiplicities. The strict positive-radius assumption is retained; Remark 1 and F3 give a counterexample at radius zero.
-- source:
--   Chen, Kuhn and Wiesemann, Technical Note—Data-Driven Chance Constrained Programs over Wasserstein Balls, Operations Research 72(1) (2024), 410–424, https://doi.org/10.1287/opre.2022.2330, Theorem 2, (5), printed pp. 414–415, PDF pp. 5–6

import Mathlib
import Definitions.Def_ChenWasserstein_Reform_Data

open MeasureTheory
open scoped ENNReal BigOperators

/- Imported declaration bodies, quoted verbatim for standalone blind auditing.
These are comments, not redeclarations or additional assumptions.

noncomputable def distUnsafe {E : Type*} [NormedAddCommGroup E] (S : Set E) (u : E) : ℝ :=
  Metric.infDist u Sᶜ

noncomputable def kthSmallest {N : ℕ} (v : Fin N → ℝ) (j : ℕ) : ℝ :=
  ((Finset.univ.val.map v).sort (· ≤ ·)).getD j 0

def IsCoupling {S : Type*} [MeasurableSpace S] (μ₁ μ₂ : Measure S) (π : Measure (S × S)) : Prop :=
  IsProbabilityMeasure π ∧ π.map Prod.fst = μ₁ ∧ π.map Prod.snd = μ₂

noncomputable def transportCost {S : Type*} [MeasurableSpace S] (c : S → S → ℝ)
    (μ₁ μ₂ : Measure S) : ℝ≥0∞ :=
  ⨅ (π : Measure (S × S)) (_ : IsCoupling μ₁ μ₂ π), ∫⁻ p, ENNReal.ofReal (c p.1 p.2) ∂π

noncomputable def worstProb {S : Type*} [MeasurableSpace S] (c : S → S → ℝ) (μ : Measure S)
    (δ : ℝ) (A : Set S) : ℝ≥0∞ :=
  ⨆ (P : Measure S) (_ : IsProbabilityMeasure P ∧ transportCost c μ P ≤ ENNReal.ofReal δ), P A

noncomputable def empiricalDistribution {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξhat : Fin N → E) : Measure E :=
  (N : ENNReal)⁻¹ • ∑ i, Measure.dirac (ξhat i)

noncomputable def fractionalSmallest {N : ℕ} (k : Fin N → ℝ) (ℓ : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (min ⌊ℓ⌋₊ N), WassDRCCP.Improved.kthSmallest k j) +
    if ⌊ℓ⌋₊ < N then
      (ℓ - (⌊ℓ⌋₊ : ℝ)) * WassDRCCP.Improved.kthSmallest k ⌊ℓ⌋₊ else 0
-/

namespace ChenWasserstein.Reform

/-- Chen, Kuhn and Wiesemann (2024), Theorem 2, (5), printed p. 414 / PDF p. 5.
Here S is the safety set S(x) at the fixed decision; no decision optimization is performed. -/
theorem theorem_2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {N : ℕ}
    (ξ : Fin N → E) (S : Set E) (ε θ : ℝ)
    (hN : 0 < N) (hε : 0 < ε) (hε1 : ε < 1) (hθ : 0 < θ)
    (hS : IsOpen S) (hC : Sᶜ.Nonempty) :
    ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ Sᶜ ≤ ENNReal.ofReal ε ↔
    θ ≤ (1 / (N : ℝ)) *
      fractionalSmallest (fun i => WassDRCCP.Improved.distUnsafe S (ξ i)) (ε * (N : ℝ)) := by sorry

end ChenWasserstein.Reform
