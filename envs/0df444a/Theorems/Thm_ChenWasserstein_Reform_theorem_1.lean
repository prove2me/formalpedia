-- Prove2me | Theorems.Thm_ChenWasserstein_Reform_theorem_1
-- name    : ChenWasserstein.Reform.theorem_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:18:52.299981+00:00
-- url     : https://prove2.me/theorems/2978ef92-3c29-4061-bd19-4d9d4b1fa9e1
-- title:
--   Theorem 1 — greedy worst-case distribution
-- statement:
--   Let $E$ be a finite-dimensional real normed space with its Borel sigma algebra, let $N\ge1$, and let $\xi_1,\ldots,\xi_N\in E$ be arbitrary samples, with repetitions permitted. Let $S\subseteq E$ be open with nonempty complement $C=E\setminus S$. Write $d_i=\inf_{y\in C}\|\xi_i-y\|$, $\widehat P=N^{-1}\sum_i\delta_{\xi_i}$, and $\mathcal F(\theta)=\{P\text{ a Borel probability law}:W_1(\widehat P,P)\le\theta\}$, where $W_1$ is the infimum of the expected norm cost over all couplings. Assume $\theta>0$.
--
--   Assume the samples are ordered so that $d_1\le\cdots\le d_N$. Choose any $\eta_i\in C$ satisfying $\|\xi_i-\eta_i\|=d_i$. Let $I$ be the number of zero distances, $D(j)=\sum_{i=1}^j d_i$, and $j^*=\max\{j\in\{0,\ldots,N\}:D(j)\le\theta N\}$. When $j^*<N$, let $p^*=(\theta N-D(j^*))/d_{j^*+1}$. Define $P^*$ by the corresponding atomic law below. Then $P^*$ is a probability law in $\mathcal F(\theta)$ and attains the worst unsafe probability:
--   $$\sup_{P\in\mathcal F(\theta)}P(C)=P^*(C).$$
--   If $j^*=N$, then
--   $$P^*=\frac1N\sum_{i=1}^{I}\delta_{\xi_i}+\frac1N\sum_{i=I+1}^{N}\delta_{\eta_i},\qquad P^*(C)=1.$$
--   If $j^*<N$, then
--   $$P^*=\frac1N\sum_{i=1}^{I}\delta_{\xi_i}+\frac1N\sum_{i=I+1}^{j^*}\delta_{\eta_i}+\frac{p^*}{N}\delta_{\eta_{j^*+1}}+\frac{1-p^*}{N}\delta_{\xi_{j^*+1}}+\frac1N\sum_{i=j^*+2}^{N}\delta_{\xi_i},\qquad P^*(C)=\frac{j^*+p^*}{N}.$$
--
--   The paper reproduces this previously established uncertainty-quantification result without proof. The assertion includes the full attaining law, not merely its value.
--
--   **Formalization Note** The nonempty unsafe set makes explicit the paper's implicit nearest-point convention (finding F1). Safety may be empty. Nearest-point selections are arbitrary and need not be unique; their existence follows from closedness, nonemptiness and finite dimension. All probability suprema and transport integrals are extended nonnegative values. No epsilon is needed in this uncertainty-quantification statement. The defined greedy law, rather than an assumed optimal law, occurs in the conclusion.
-- source:
--   Chen, Kuhn and Wiesemann, Technical Note—Data-Driven Chance Constrained Programs over Wasserstein Balls, Operations Research 72(1) (2024), 410–424, https://doi.org/10.1287/opre.2022.2330, Theorem 1, printed p. 413, PDF p. 4

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

noncomputable def prefixSum {N : ℕ} (d : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i : Fin N, if i.val < j then d i else 0

noncomputable def zeroCount {N : ℕ} (d : Fin N → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => d i = 0)).card

noncomputable def jStar {N : ℕ} (d : Fin N → ℝ) (θ : ℝ) : ℕ :=
  ((Finset.range (N + 1)).filter (fun j => prefixSum d j ≤ θ * (N : ℝ))).sup id

noncomputable def pStar {N : ℕ} (d : Fin N → ℝ) (θ : ℝ) : ℝ :=
  if h : jStar d θ < N then
    (θ * (N : ℝ) - prefixSum d (jStar d θ)) / d ⟨jStar d θ, h⟩
  else 0

noncomputable def fullLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) : Measure E :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N,
    if i.val < zeroCount d then Measure.dirac (ξ i) else Measure.dirac (η i)

noncomputable def partialLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) (θ : ℝ) : Measure E :=
  (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N,
    if i.val < zeroCount d then Measure.dirac (ξ i)
    else if i.val < jStar d θ then Measure.dirac (η i)
    else if i.val = jStar d θ then
      ENNReal.ofReal (pStar d θ) • Measure.dirac (η i) +
        ENNReal.ofReal (1 - pStar d θ) • Measure.dirac (ξ i)
    else Measure.dirac (ξ i)

noncomputable def greedyLaw {E : Type*} [MeasurableSpace E] {N : ℕ}
    (ξ η : Fin N → E) (d : Fin N → ℝ) (θ : ℝ) : Measure E :=
  if jStar d θ = N then fullLaw ξ η d else partialLaw ξ η d θ
-/

namespace ChenWasserstein.Reform

/-- Chen, Kuhn and Wiesemann (2024), Theorem 1, printed p. 413 / PDF p. 4.
The samples are ordered by distance. η is any selection of closest unsafe points.
The nonempty complement states the source's implicit nearest-point domain. -/
theorem theorem_1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {N : ℕ}
    (ξ η : Fin N → E) (S : Set E) (θ : ℝ)
    (hN : 0 < N) (hθ : 0 < θ) (hS : IsOpen S) (hC : Sᶜ.Nonempty)
    (horder : Monotone (fun i => WassDRCCP.Improved.distUnsafe S (ξ i)))
    (hη : ∀ i, η i ∈ Sᶜ ∧ ‖ξ i - η i‖ = WassDRCCP.Improved.distUnsafe S (ξ i)) :
    let d := fun i => WassDRCCP.Improved.distUnsafe S (ξ i)
    let P := greedyLaw ξ η d θ
    IsProbabilityMeasure P ∧
    ModelRiskOT.WorstProb.transportCost (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) P ≤ ENNReal.ofReal θ ∧
    ModelRiskOT.WorstProb.worstProb (fun u v : E => ‖u - v‖)
      (WassersteinDRO.Duality.empiricalDistribution ξ) θ Sᶜ = P Sᶜ ∧
    (jStar d θ = N → P = fullLaw ξ η d ∧ P Sᶜ = 1) ∧
    (jStar d θ < N → P = partialLaw ξ η d θ ∧
      P Sᶜ = ENNReal.ofReal (((jStar d θ : ℕ) : ℝ) + pStar d θ) / (N : ℝ≥0∞)) := by sorry

end ChenWasserstein.Reform
