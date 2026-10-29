-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_theorem_2
-- name    : CohenPriceFairness.LocalWelfare.theorem_2
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:33.455872+00:00
-- url     : https://prove2.me/theorems/d5face5a-2463-4b5d-9b95-091d8ecfc3d4
-- title:
--   Theorem 2 — impact of imposing a little fairness on social welfare
-- statement:
--   Consider a seller with unlimited supply, two groups of positive real population masses $d_i$, common marginal cost $c\ge0$, and all nonnegative real prices. Both groups have either uniform valuations on $[0,b_i]$ with $b_i>0$, $b_0\ne b_1$, or exponential valuations of rates $\lambda_i>0$, $\lambda_0\ne\lambda_1$. Purchase occurs at valuation at least price. Profit, consumer surplus and nonbuyer valuation are derived from these laws.
--
--   There exists an unconstrained global optimum for each group. For every pair of baseline optima, and separately for each of the four metrics, local selections of global profit-maximizing fair price pairs anchored at that baseline exist. For every such selection, the finite right derivative at zero of social welfare exists and obeys the printed strict signs:
--   $$D_{\rm price}>0,\qquad D_{\rm nonbuyer}>0,\qquad D_{\rm demand}<0,\qquad D_{\rm surplus}<0.$$
--   Here fairness means $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(p_0^*)-M_1(p_1^*)|$ with $\alpha\in[0,1]$, and welfare is total profit plus $d_0S_0(p_0)+d_1S_1(p_1)$. All eight family/metric cases are included, without excluding zero cost, high cost, zero baseline gaps, below-cost prices, or absent sales.
--
--   This is the source's claim, retained as a statement to resolve. The counterexamples in the accompanying insights are not removed by extra hypotheses or by weakening a strict sign.
--
--   Differences from the source:
--   - encoding: two customer populations → two positive real masses indexed by Fin 2, without normalization; reason: two nonempty groups are implicit on pp. 6–7; this retains unequal and noninteger populations
--   - reading: the total-surplus displays on pp. 8 and 12 repeat S₁ → total surplus is d₀S₀(p₀)+d₁S₁(p₁); reason: the group welfare definition on p. 7 and proof on p. 31 establish the intended index; insight I2
--   - reading: conditional mean Nᵢ is undefined when there are no nonbuyers → Nᵢ is explicitly zero when the conditioning event has probability zero; reason: Eq. (1) admits zero prices; this is the right-continuous extension for the goal families and changes no ordinary conditional mean; insight I5
--   - reading: optimal prices are named without a tie rule → every baseline optimum and every local optimal selection anchored there are covered, with constrained-selection existence explicit; reason: the tie-independent reading prevents a convenient optimizer choice or an absent selection from hiding a case
--   - encoding: the right derivative is written as a finite right limit → existence of a real D and convergence of the difference quotient from strictly positive alpha; reason: the footnote 7 limit is preserved without using a default-valued derivative at a nonexistent limit
--   - encoding: unconstrained optimal prices are denoted by argmax → existence of a pair of global baseline maximizers is an explicit conclusion; reason: this exposes the existence implicit in the source instead of assuming it or letting universal baseline quantification be vacuous
-- source:
--   Cohen, Elmachtoub and Lei (2022), Price Discrimination with Fairness Constraints, Management Science, https://doi.org/10.1287/mnsc.2022.4317; published artifact, PDF pages = printed pages; SHA-256 b3f8804f1610eb36d8a2ef32e836f4a65285e6b8ad427f7c82172e7a3fd73147; §2.3, Theorem 2, p. 12; model §§2–2.1, pp. 6–8; proof p. 33.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

namespace CohenPriceFairness.LocalWelfare

/-- The full printed Theorem 2 (p. 12), including its strict signs at zero and high costs. -/
theorem theorem_2 (m : Market) (hd : ∀ i, 0 < m.population i)
    (hc : 0 ≤ m.cost) (hf : Families m) :
    (∃ b : Prices, BaselineOptimal m b) ∧
    ∀ b : Prices, BaselineOptimal m b →
      SensitivityClaim m b .price (fun D => 0 < D) ∧
      SensitivityClaim m b .nonbuyer (fun D => 0 < D) ∧
      SensitivityClaim m b .demand (fun D => D < 0) ∧
      SensitivityClaim m b .surplus (fun D => D < 0) := by sorry

end CohenPriceFairness.LocalWelfare

/- Imported definition source (verbatim dependency snapshot for standalone inspection).

import Mathlib

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- A nonnegative valuation law with a finite first moment (pp. 6–7). -/
def ValuationLaw (μ : Measure ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ v ∂μ, 0 ≤ v) ∧ Integrable (fun v : ℝ => v) μ

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_ValuationLaw

open MeasureTheory

namespace CohenPriceFairness.LocalWelfare

/-- Two marginal valuation laws, real population masses, and common marginal cost. -/
structure Market where
  law : Fin 2 → Measure ℝ
  population : Fin 2 → ℝ
  cost : ℝ

/-- The general distribution-based market conventions, pp. 6–7. -/
def Market.Admissible (m : Market) : Prop :=
  0 ≤ m.cost ∧ ∀ i, 0 < m.population i ∧ ValuationLaw (m.law i)

noncomputable def demand (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  (m.law i (Set.Ici p)).toReal

noncomputable def surplus (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  ∫ v, max (v - p) 0 ∂m.law i

/-- Conditional mean of nonbuyers; explicitly zero on a null conditioning event. -/
noncomputable def nonbuyer (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  if m.law i (Set.Iio p) = 0 then 0
  else (∫ v in Set.Iio p, v ∂m.law i) / (m.law i (Set.Iio p)).toReal

noncomputable def profit (m : Market) (i : Fin 2) (p : ℝ) : ℝ :=
  m.population i * (p - m.cost) * demand m i p

abbrev Prices := Fin 2 → ℝ

noncomputable def totalProfit (m : Market) (p : Prices) : ℝ :=
  profit m 0 (p 0) + profit m 1 (p 1)

/-- Group-specific surplus indices, as on pp. 7 and 31. -/
noncomputable def welfare (m : Market) (p : Prices) : ℝ :=
  totalProfit m p + m.population 0 * surplus m 0 (p 0) +
    m.population 1 * surplus m 1 (p 1)

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Market

namespace CohenPriceFairness.LocalWelfare

inductive Metric where
  | price | demand | surplus | nonbuyer
  deriving DecidableEq

noncomputable def metricValue (m : Market) : Metric → Fin 2 → ℝ → ℝ
  | .price => fun _ p => p
  | .demand => demand m
  | .surplus => surplus m
  | .nonbuyer => nonbuyer m

/-- All individual global maximizers on nonnegative prices. -/
def BaselineOptimal (m : Market) (b : Prices) : Prop :=
  ∀ i, 0 ≤ b i ∧ ∀ p : ℝ, 0 ≤ p → profit m i p ≤ profit m i (b i)

noncomputable def gap (m : Market) (k : Metric) (p : Prices) : ℝ :=
  |metricValue m k 0 (p 0) - metricValue m k 1 (p 1)|

/-- Equation (1), including its full parameter and price domains. -/
def FairFeasible (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  α ∈ Set.Icc 0 1 ∧ (∀ i, 0 ≤ p i) ∧ gap m k p ≤ (1 - α) * gap m k b

/-- The optimum set is defined by comparison against every feasible price pair. -/
def FairOptimal (m : Market) (b : Prices) (k : Metric) (α : ℝ) (p : Prices) : Prop :=
  FairFeasible m b k α p ∧
    ∀ q : Prices, FairFeasible m b k α q → totalProfit m q ≤ totalProfit m p

/-- A selection of actual optima on some right neighborhood, anchored at the baseline.
No continuity or differentiability, and no restriction to active price neighborhoods. -/
def LocalOptimalSelection (m : Market) (b : Prices) (k : Metric)
    (P : ℝ → Prices) : Prop :=
  P 0 = b ∧ ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
    ∀ α ∈ Set.Icc 0 ε, FairOptimal m b k α (P α)

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_FairPricing

open Filter Topology

namespace CohenPriceFairness.LocalWelfare

/-- The finite right derivative in footnote 7, p. 12. -/
def RightDerivative (f : ℝ → ℝ) (D : ℝ) : Prop :=
  Tendsto (fun α : ℝ => (f α - f 0) / α) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 D)

/-- Differentiability in a neighborhood and differentiability of the derivative at x.
Continuity at x follows; continuity of the second derivative is not assumed. -/
def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  (∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) ∧ DifferentiableAt ℝ (deriv f) x

/-- Monotonicity and an inverse on the image of an open active interval at x.
No derivative condition on the inverse or nonzero derivative is imposed. -/
def ActiveInvertible (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ l u : ℝ, l < x ∧ x < u ∧
    (MonotoneOn f (Set.Ioo l u) ∨ AntitoneOn f (Set.Ioo l u)) ∧
    ∃ g : ℝ → ℝ,
      (∀ p ∈ Set.Ioo l u, g (f p) = p) ∧
      (∀ y ∈ f '' Set.Ioo l u, g y ∈ Set.Ioo l u ∧ f (g y) = y)

/-- Exactly the local regularity of Lemma 1 for all four source functions. -/
def LemmaRegularity (m : Market) (b : Prices) : Prop :=
  ∀ i,
    TwiceDifferentiableAt (demand m i) (b i) ∧
    TwiceDifferentiableAt (surplus m i) (b i) ∧
    TwiceDifferentiableAt (nonbuyer m i) (b i) ∧
    TwiceDifferentiableAt (profit m i) (b i) ∧
    ActiveInvertible (demand m i) (b i) ∧
    ActiveInvertible (surplus m i) (b i) ∧
    ActiveInvertible (nonbuyer m i) (b i)

/-- Existence of a policy, and the specified finite-derivative assertion for every policy. -/
def SensitivityClaim (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop) : Prop :=
  (∃ P : ℝ → Prices, LocalOptimalSelection m b k P) ∧
    ∀ P : ℝ → Prices, LocalOptimalSelection m b k P →
      ∃ D : ℝ, RightDerivative (fun α => welfare m (P α)) D ∧ C D

end CohenPriceFairness.LocalWelfare

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Market

open MeasureTheory ProbabilityTheory

namespace CohenPriceFairness.LocalWelfare

/-- Uniform probability on [0,b] for positive b: normalized restricted Lebesgue measure. -/
noncomputable def uniformLaw (b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal b)⁻¹ • volume.restrict (Set.Icc 0 b)

/-- Both groups use the same one of the two continuous families, with unequal parameters. -/
def Families (m : Market) : Prop :=
  (∃ b : Fin 2 → ℝ, (∀ i, 0 < b i) ∧ b 0 ≠ b 1 ∧
    ∀ i, m.law i = uniformLaw (b i)) ∨
  (∃ rate : Fin 2 → ℝ, (∀ i, 0 < rate i) ∧ rate 0 ≠ rate 1 ∧
    ∀ i, m.law i = expMeasure (rate i))

end CohenPriceFairness.LocalWelfare
-/
