-- Prove2me | Theorems.Thm_BramsonQueueing_Fluid_theorem_4_16
-- name    : BramsonQueueing.Fluid.theorem_4_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:23:10.561464+00:00
-- url     : https://prove2.me/theorems/98f370bd-0a5e-4923-95c0-340a0f7fcd4c
-- title:
--   Theorem 4.16 — Stable fluid limits imply positive Harris recurrence
-- statement:
--   Let an HL queueing network have the general renewal and service primitives of Section 4.1, with its full state size $|x|=|z|+|u|+|v|$. Suppose every sublevel set
--   $$A_\kappa=\{x:|x|\le\kappa\},\qquad\kappa>0,$$
--   is petite. If its associated family of fluid limits is stable, meaning one $N>0$ drains every fluid-limit queue trajectory at all times $t\ge N|\overline Z(0)|$, then
--   $$\text{the queueing network is positive Harris recurrent}.$$
--   In particular, the network is positive Harris recurrent whenever any associated fluid model is stable. Association includes the existence of an appropriate convergent subsequence for every admissible scaling sequence.
--
--   Stability here is Harris recurrence together with an invariant probability measure, independently defined using occupation times and the transition semigroup. The theorem adds no Poisson, phase-type, Feller, second-moment, or positive-total-arrival assumption.
--
--   Differences from the source:
--   - encoding: classes 1 through K and stations 1 through J → Fin K and Fin J, with positive cardinalities and an onto station assignment; reason: this only relabels the finite classes and nonempty stations; queue populations remain unbounded
--   - encoding: nonnegative real times and nonnegative quantities → NNReal times and quantities; reason: the subtype has the same domain, including zero
--   - encoding: the full HL state and primitive-driven process of Sections 4.1 and 4.3 → an equivalent ordered-list state presentation and an axiomatic realization of that evolution; reason: the coordinate equivalence includes every source state; the fields specify dynamics and Markov regularity, not stability conclusions
--   - encoding: a finite nonzero stationary measure in the definition of positive Harris recurrence → an invariant probability measure together with occupation-time Harris recurrence; reason: normalizing the finite stationary measure is equivalent
--   - encoding: the universally completed natural filtration in (4.5) → usual completed filtrations indexed by the starting state, with explicit strong Markov identities; reason: the canonical Markov family admits these completed starting-state realizations with the same paths and transition laws
--   - encoding: the primitive construction for each initial state in Section 4.1 and the common event G in (4.70) → one probability space of positive primitive sequences, with the initial state a parameter of the paths; reason: the iid primitive laws do not depend on the initial state; positive versions can be realized on their positive product space and completed without restricting any permitted law
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), https://doi.org/10.1007/978-3-540-68896-9; published edition; Theorem 4.16, printed 121 / PDF 129.

import Definitions.Def_BramsonQueueing_Fluid_FluidLimits

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

theorem theorem_4_16 {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]
    (n : HLNetwork d S Ω)
    (hpetite : ∀ κ : ℝ≥0, 0 < κ → Petite n.process {x | n.size x ≤ κ}) :
    (FluidLimitsStable n → PositiveHarris n.process) ∧
    (∀ model : FluidModel d, Associated n model → model.Stable → PositiveHarris n.process) := by sorry

end BramsonQueueing.Fluid

/- BEGIN VERBATIM DEPENDENCY CONTEXT
Transitive imported Lean code for standalone blind auditing.
The following text is verbatim dependency code in a comment, not additional declarations.

MODULE Def_BramsonQueueing_Fluid_NetworkData
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Finite classes and stations, with open substochastic routing. No restriction
on the number of jobs, and no positivity requirement on total arrival rates. -/
structure NetworkData (K J : ℕ) where
  classes_pos : 0 < K
  stations_pos : 0 < J
  station : Fin K → Fin J
  station_surjective : Function.Surjective station
  external : Finset (Fin K)
  alpha : Fin K → ℝ
  alpha_pos : ∀ k ∈ external, 0 < alpha k
  alpha_zero : ∀ k ∉ external, alpha k = 0
  meanService : Fin K → ℝ
  meanService_pos : ∀ k, 0 < meanService k
  routing : Matrix (Fin K) (Fin K) ℝ
  routing_nonneg : ∀ k l, 0 ≤ routing k l
  routing_substochastic : ∀ k, ∑ l, routing k l ≤ 1
  routing_open : ∀ k l, Summable (fun n : ℕ => (routing.transpose ^ n) k l)

noncomputable def routingPotential {K J : ℕ} (d : NetworkData K J) :
    Matrix (Fin K) (Fin K) ℝ := fun k l => ∑' n : ℕ, (d.routing.transpose ^ n) k l

noncomputable def totalArrival {K J : ℕ} (d : NetworkData K J) (k : Fin K) : ℝ :=
  ∑ l, routingPotential d k l * d.alpha l

noncomputable def traffic {K J : ℕ} (d : NetworkData K J) (j : Fin J) : ℝ :=
  ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), d.meanService k * totalArrival d k

def Subcritical {K J : ℕ} (d : NetworkData K J) : Prop := ∀ j, traffic d j < 1

noncomputable def mass {K : ℕ} (z : Fin K → ℝ) : ℝ := ∑ k, |z k|

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_FluidModel
import Definitions.Def_BramsonQueueing_Fluid_NetworkData

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- The six components in (4.40), on nonnegative real time. -/
structure SixPath (K J : ℕ) where
  A : ℝ≥0 → Fin K → ℝ
  D : ℝ≥0 → Fin K → ℝ
  T : ℝ≥0 → Fin K → ℝ
  W : ℝ≥0 → Fin J → ℝ
  Y : ℝ≥0 → Fin J → ℝ
  Z : ℝ≥0 → Fin K → ℝ

/-- Nonnegativity and monotonicity required in §4.3. -/
def FluidRegular {K J : ℕ} (q : SixPath K J) : Prop :=
  (∀ t k, 0 ≤ q.A t k ∧ 0 ≤ q.D t k ∧ 0 ≤ q.T t k ∧ 0 ≤ q.Z t k) ∧
  (∀ t j, 0 ≤ q.W t j ∧ 0 ≤ q.Y t j) ∧
  (∀ k, Monotone (fun t => q.A t k) ∧ Monotone (fun t => q.D t k) ∧
    Monotone (fun t => q.T t k)) ∧
  (∀ j, Monotone (fun t => q.Y t j))

/-- The basic fluid equations (4.50)–(4.55). The support formulation of
nonidling is the source's definition of "can only increase when W = 0".
Continuity follows from the equations; it is not an additional hypothesis. -/
def BasicFluid {K J : ℕ} (d : NetworkData K J) (q : SixPath K J) : Prop :=
  FluidRegular q ∧
  (∀ t k, q.A t k = d.alpha k * t + ∑ l, d.routing l k * q.D t l) ∧
  (∀ t k, q.Z t k = q.Z 0 k + q.A t k - q.D t k) ∧
  (∀ t j, q.W t j =
    (∑ k ∈ Finset.univ.filter (fun k => d.station k = j),
      d.meanService k * (q.Z 0 k + q.A t k)) -
    ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), q.T t k) ∧
  (∀ t j, (∑ k ∈ Finset.univ.filter (fun k => d.station k = j), q.T t k) +
    q.Y t j = t) ∧
  (∀ j s t, s ≤ t → q.Y s j < q.Y t j →
    ∃ u ∈ Set.Icc s t, q.W u j = 0) ∧
  (∀ t k, q.T t k = d.meanService k * q.D t k)

/-- A model adds any discipline equations to the basic equations. -/
structure FluidModel {K J : ℕ} (d : NetworkData K J) where
  auxiliary : SixPath K J → Prop

def FluidModel.Solution {K J : ℕ} {d : NetworkData K J}
    (model : FluidModel d) (q : SixPath K J) : Prop :=
  BasicFluid d q ∧ model.auxiliary q

def basicModel {K J : ℕ} (d : NetworkData K J) : FluidModel d := ⟨fun _ => True⟩

/-- One draining coefficient, uniform over all solutions, including zero initial mass. -/
def StableFamily {K J : ℕ} (F : SixPath K J → Prop) : Prop :=
  ∃ N : ℝ, 0 < N ∧ ∀ q, F q → ∀ t : ℝ≥0,
    N * mass (q.Z 0) ≤ t → q.Z t = 0

def FluidModel.Stable {K J : ℕ} {d : NetworkData K J} (model : FluidModel d) : Prop :=
  StableFamily model.Solution

/-- Uniform convergence on every compact time interval of all six components. -/
def SixUOC {K J : ℕ} (f : ℕ → SixPath K J) (q : SixPath K J) : Prop :=
  ∀ H : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ t ≤ H,
    (∀ k, |(f n).A t k - q.A t k| < ε ∧ |(f n).D t k - q.D t k| < ε ∧
      |(f n).T t k - q.T t k| < ε ∧ |(f n).Z t k - q.Z t k| < ε) ∧
    (∀ j, |(f n).W t j - q.W t j| < ε ∧ |(f n).Y t j - q.Y t j| < ε)

noncomputable def scaleSix {K J : ℕ} (a : ℝ≥0) (q : SixPath K J) : SixPath K J where
  A t k := q.A (a * t) k / a
  D t k := q.D (a * t) k / a
  T t k := q.T (a * t) k / a
  W t j := q.W (a * t) j / a
  Y t j := q.Y (a * t) j / a
  Z t k := q.Z (a * t) k / a

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_MarkovProcess
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace BramsonQueueing.Fluid

/-- A right continuous strong Markov family on a locally compact separable
metric Borel space. The filtration has the usual null-set and right continuity
properties. Strong Markov is stated as the integral identity at stopping times,
on their finite part, so no recurrence or moment conclusion is a field. -/
structure MarkovProcess (S Ω : Type*) [MetricSpace S] [MeasurableSpace S]
    [BorelSpace S] [LocallyCompactSpace S] [SecondCountableTopology S]
    [MeasurableSpace Ω] where
  law : S → Measure Ω
  probability : ∀ x, IsProbabilityMeasure (law x)
  X : S → ℝ≥0 → Ω → S
  filtration : S → Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)
  adapted : ∀ x t, Measurable[filtration x t] (X x t)
  jointly_measurable : ∀ x, Measurable (fun p : ℝ≥0 × Ω => X x p.1 p.2)
  initial : ∀ x, ∀ᵐ ω ∂law x, X x 0 ω = x
  right_continuous : ∀ x, ∀ᵐ ω ∂law x, ∀ t,
    ContinuousWithinAt (fun s => X x s ω) (Set.Ici t) t
  complete : ∀ x t (A B : Set Ω), MeasurableSet B → law x B = 0 → A ⊆ B →
    MeasurableSet[filtration x t] A
  filtration_right_continuous : ∀ x t, filtration x t = ⨅ s > t, filtration x s
  transition : ℝ≥0 → S → Measure S
  transition_probability : ∀ t x, IsProbabilityMeasure (transition t x)
  transition_measurable : ∀ B : Set S, MeasurableSet B →
    Measurable (fun p : ℝ≥0 × S => transition p.1 p.2 B)
  transition_law : ∀ x t B, MeasurableSet B →
    transition t x B = law x {ω | X x t ω ∈ B}
  semigroup : ∀ s t x B, MeasurableSet B →
    transition (s + t) x B = ∫⁻ y, transition t y B ∂transition s x
  strong_markov : ∀ x (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (filtration x) τ) (t : ℝ≥0) (A : Set Ω)
    (B : Set S), MeasurableSet[hτ.measurableSpace] A → MeasurableSet B →
    (∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤},
      Set.indicator B (fun _ => (1 : ℝ≥0∞)) (X x ((τ ω).untopD 0 + t) ω) ∂law x) =
    ∫⁻ ω in A ∩ {ω | τ ω ≠ ⊤}, transition t (X x ((τ ω).untopD 0) ω) B ∂law x

variable {S Ω : Type*} [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- Hitting time with delay, including infinity when the set is never visited. -/
noncomputable def hittingTime (p : MarkovProcess S Ω) (A : Set S)
    (δ : ℝ≥0) (x : S) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : δ ≤ t) (_ : p.X x t ω ∈ A), (t : ℝ≥0∞)

noncomputable def expectedHitting (p : MarkovProcess S Ω) (A : Set S)
    (δ : ℝ≥0) (x : S) : ℝ≥0∞ := ∫⁻ ω, hittingTime p A δ x ω ∂p.law x

noncomputable def occupation (p : MarkovProcess S Ω) (A : Set S)
    (x : S) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Set.Ici 0,
    Set.indicator A (fun _ => (1 : ℝ≥0∞)) (p.X x t.toNNReal ω)

/-- Harris recurrence is occupation of every positive irreducibility-measure set
for infinite time, not a Foster criterion. -/
def Harris (p : MarkovProcess S Ω) : Prop :=
  ∃ φ : Measure S, φ ≠ 0 ∧ SigmaFinite φ ∧
    ∀ A : Set S, MeasurableSet A → 0 < φ A →
      ∀ x, p.law x {ω | occupation p A x ω = ⊤} = 1

def Invariant (p : MarkovProcess S Ω) (π : Measure S) : Prop :=
  ∀ t A, MeasurableSet A → π A = ∫⁻ x, p.transition t x A ∂π

def PositiveHarris (p : MarkovProcess S Ω) : Prop :=
  Harris p ∧ ∃ π : Measure S, IsProbabilityMeasure π ∧ Invariant p π

/-- Nonempty measurable petite set, with its sampling law supported on positive times. -/
def Petite (p : MarkovProcess S Ω) (A : Set S) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧
  ∃ a : Measure ℝ≥0, IsProbabilityMeasure a ∧ a {0} = 0 ∧
  ∃ ν : Measure S, ν ≠ 0 ∧ ∀ x ∈ A, ∀ B : Set S, MeasurableSet B →
    ν B ≤ ∫⁻ t, p.transition t x B ∂a

def UniformlySmall (p : MarkovProcess S Ω) (A : Set S) (s₁ s₂ : ℝ≥0) : Prop :=
  A.Nonempty ∧ MeasurableSet A ∧ ∃ ν : Measure S, ν ≠ 0 ∧
    ∀ t ∈ Set.Icc s₁ s₂, ∀ x ∈ A, ∀ B : Set S, MeasurableSet B →
      ν B ≤ p.transition t x B

/-- Total variation convergence, expressed by its uniform measurable-event bound. -/
def Ergodic (p : MarkovProcess S Ω) : Prop :=
  ∃ π : Measure S, IsProbabilityMeasure π ∧ Invariant p π ∧
    ∀ x, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ≥0, ∀ t ≥ T, ∀ B : Set S,
      MeasurableSet B → |(p.transition t x B).toReal - (π B).toReal| < ε

noncomputable def expectedSize (p : MarkovProcess S Ω) (size : S → ℝ≥0)
    (x : S) (t : ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, (size (p.X x t ω) : ℝ≥0∞) ∂p.law x

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_Renewal
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Positive iid finite-mean increments; indices zero, one, ... encode the
source's indices one, two, ... . No higher moment or density assumption. -/
structure PositiveIID (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) where
  beta : ℕ → Ω → ℝ≥0
  measurable : ∀ n, Measurable (beta n)
  positive : ∀ n, ∀ᵐ ω ∂μ, 0 < beta n ω
  independent : iIndepFun beta μ
  identically_distributed : ∀ n, IdentDistrib (beta n) (beta 0) μ μ
  finite_mean : Integrable (fun ω => (beta 0 ω : ℝ)) μ

noncomputable def renewalMean {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) : ℝ := ∫ ω, (r.beta 0 ω : ℝ) ∂μ

noncomputable def renewalSum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (n : ℕ) (ω : Ω) : ℝ≥0 := ∑ i ∈ Finset.range n, r.beta i ω

def RenewalGood {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (ω : Ω) : Prop :=
  Tendsto (fun n : ℕ => (renewalSum r n ω : ℝ) / n) atTop (𝓝 (renewalMean r))

/-- The count includes the first pending increment. Infinite exceptional counts
are retained, rather than a natural or real supremum's default value. -/
noncomputable def renewalB1 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (⨆ n : ℕ, ⨆ (_ : renewalSum r n ω ≤ t), ((n + 1 : ℕ) : ℝ≥0∞)) / t

noncomputable def renewalB2 {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (⨆ n : ℕ, ⨆ (_ : renewalSum r n ω ≤ t), (r.beta n ω : ℝ≥0∞)) / t

/-- Uniform tail expectation tending to zero, written without a real supremum. -/
def UniformTail {I Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : I → Ω → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ M₀ : ℝ≥0, ∀ M ≥ M₀, ∀ i,
    (∫⁻ ω in {ω | (M : ℝ≥0∞) ≤ F i ω}, F i ω ∂μ) ≤ ε

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_HLState
import Definitions.Def_BramsonQueueing_Fluid_NetworkData

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Finite ordered job lists allow arbitrarily many jobs. Ages are times since
entry to the present class. The remaining coordinates are residual times and
the fractions of station effort assigned to each class's oldest job. -/
structure StateData (K : ℕ) where
  jobs : List (Fin K × ℝ≥0)
  u : Fin K → ℝ≥0
  v : Fin K → ℝ≥0
  r : Fin K → ℝ≥0

def queueCount {K : ℕ} (s : StateData K) (k : Fin K) : ℕ :=
  (s.jobs.filter (fun a => a.1 = k)).length

def ValidState {K J : ℕ} (d : NetworkData K J) (s : StateData K) : Prop :=
  s.jobs.Pairwise (fun a b => b.2 < a.2 ∨ (a.2 = b.2 ∧ a.1 ≤ b.1)) ∧
  (∀ k, (k ∈ d.external → 0 < s.u k) ∧ (k ∉ d.external → s.u k = 0)) ∧
  (∀ k, (queueCount s k = 0 → s.v k = 0 ∧ s.r k = 0) ∧
    (0 < queueCount s k → 0 < s.v k) ∧ s.r k ≤ 1) ∧
  (∀ j, (∃ k, d.station k = j ∧ 0 < queueCount s k) →
    ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), s.r k = 1)

def stateSize {K : ℕ} (s : StateData K) : ℝ≥0 :=
  s.jobs.length + ∑ k, s.u k + ∑ k, s.v k

/-- Coordinates used by the source metric (4.2), including per-job service rates. -/
noncomputable def jobCoordinates {K : ℕ} (s : StateData K) (i : ℕ) : ℝ × ℝ × ℝ :=
  match s.jobs[i]? with
  | none => (0, 0, 0)
  | some a => ((a.1.val + 1 : ℕ), a.2,
      if ∃ b ∈ s.jobs.take i, b.1 = a.1 then 0 else s.r a.1)

noncomputable def stateDistance {K : ℕ} (s s' : StateData K) : ℝ :=
  (∑ i ∈ Finset.range (max s.jobs.length s'.jobs.length),
    min (|(jobCoordinates s i).1 - (jobCoordinates s' i).1| +
      |(jobCoordinates s i).2.1 - (jobCoordinates s' i).2.1| +
      |(jobCoordinates s i).2.2 - (jobCoordinates s' i).2.2|) 1) +
  (∑ k, |(s.u k : ℝ) - s'.u k|) + (∑ k, |(s.v k : ℝ) - s'.v k|)

/-- An arbitrary presentation of exactly the full state space (4.1)–(4.3).
The equivalence ensures no initial states or unbounded queues are omitted. -/
structure StatePresentation {K J : ℕ} (d : NetworkData K J) (S : Type*)
    [MetricSpace S] [MeasurableSpace S] where
  coordinates : S ≃ {s : StateData K // ValidState d s}
  metric : ∀ x y, dist x y = stateDistance (coordinates x).1 (coordinates y).1
  measurable_u : ∀ k, Measurable (fun x => (coordinates x).1.u k)
  measurable_v : ∀ k, Measurable (fun x => (coordinates x).1.v k)
  measurable_r : ∀ k, Measurable (fun x => (coordinates x).1.r k)
  measurable_z : ∀ k, Measurable (fun x => queueCount (coordinates x).1 k)
  size_continuous : Continuous (fun x => stateSize (coordinates x).1)

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_Primitives
import Definitions.Def_BramsonQueueing_Fluid_NetworkData
import Definitions.Def_BramsonQueueing_Fluid_Renewal

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

instance routeMeasurableSpace (K : ℕ) : MeasurableSpace (Option (Fin K)) := ⊤

abbrev PrimitiveIndex {K J : ℕ} (d : NetworkData K J) :=
  {k : Fin K // k ∈ d.external} ⊕ (Fin K ⊕ Fin K)

/-- Real coding used solely to express independence of all primitive sequences. -/
noncomputable def primitiveCode {K J : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {d : NetworkData K J}
    (xi : {k : Fin K // k ∈ d.external} → PositiveIID Ω μ)
    (gamma : Fin K → PositiveIID Ω μ) (route : Fin K → ℕ → Ω → Option (Fin K))
    (i : PrimitiveIndex d) (ω : Ω) (n : ℕ) : ℝ :=
  match i with
  | .inl k => (xi k).beta n ω
  | .inr (.inl k) => (gamma k).beta n ω
  | .inr (.inr k) => match route k n ω with
    | none => 0
    | some l => l.val + 1

/-- Independent iid renewal/service/routing sequences with the source means.
Routing selects one new class or departure, not a general branching network. -/
structure PrimitiveTriple {K J : ℕ} (d : NetworkData K J) (Ω : Type*)
    [MeasurableSpace Ω] (μ : Measure Ω) where
  probability : IsProbabilityMeasure μ
  xi : {k : Fin K // k ∈ d.external} → PositiveIID Ω μ
  gamma : Fin K → PositiveIID Ω μ
  xi_positive : ∀ k n ω, 0 < (xi k).beta n ω
  gamma_positive : ∀ k n ω, 0 < (gamma k).beta n ω
  xi_mean : ∀ k, renewalMean (xi k) = 1 / d.alpha k
  gamma_mean : ∀ k, renewalMean (gamma k) = d.meanService k
  route : Fin K → ℕ → Ω → Option (Fin K)
  route_measurable : ∀ k n, Measurable (route k n)
  route_independent : ∀ k, iIndepFun (route k) μ
  route_identically_distributed : ∀ k n, IdentDistrib (route k n) (route k 0) μ μ
  route_law : ∀ k l, μ {ω | route k 0 ω = some l} = ENNReal.ofReal (d.routing k l)
  sequences_independent : iIndepFun (primitiveCode xi gamma route) μ

noncomputable def routingCount {K J : ℕ} {d : NetworkData K J} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (p : PrimitiveTriple d Ω μ)
    (k l : Fin K) (n : ℕ) (ω : Ω) : ℕ :=
  ((Finset.range n).filter (fun i => p.route k i ω = some l)).card

/-- The common strong-law event (4.70), defined from primitives, not limits. -/
def PrimitiveGood {K J : ℕ} {d : NetworkData K J} {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω} (p : PrimitiveTriple d Ω μ) (ω : Ω) : Prop :=
  (∀ k, RenewalGood (p.xi k) ω) ∧ (∀ k, RenewalGood (p.gamma k) ω) ∧
    ∀ k l, Tendsto (fun n : ℕ => (routingCount p k l n ω : ℝ) / n)
      atTop (𝓝 (d.routing k l))

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_HLNetwork
import Definitions.Def_BramsonQueueing_Fluid_HLState
import Definitions.Def_BramsonQueueing_Fluid_MarkovProcess
import Definitions.Def_BramsonQueueing_Fluid_Primitives
import Definitions.Def_BramsonQueueing_Fluid_FluidModel

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

/-- Cumulative work of the first n jobs to be served at a class. If initially
nonempty, the oldest job uses its residual service; otherwise all jobs use fresh
service times. In particular the zero-job cumulative work is exactly zero. -/
noncomputable def serviceWork {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (z : ℕ) (v : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  if z = 0 then renewalSum r n ω
  else if n = 0 then 0 else v + renewalSum r (n - 1) ω

noncomputable def externalCount {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (r : PositiveIID Ω μ) (u t : ℝ≥0) (ω : Ω) : ℕ :=
  sSup {n : ℕ | n = 0 ∨ u + renewalSum r (n - 1) ω ≤ t}

/-- Under its strong-law hypothesis the set above is finite. The source's next
renewal epoch, after e external arrivals, is u plus e fresh increments. -/
noncomputable def arrivalAge (A : ℝ≥0 → ℕ) (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  t - sInf {s : ℝ≥0 | n ≤ A s}

variable {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
  [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- A source HL network as an axiomatic realization of its primitive-driven
evolution. Fields describe the construction and the system equations, never
fluid limits, recurrence, drift, integrability bounds, or stability. -/
structure HLNetwork (d : NetworkData K J) (S Ω : Type*)
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω] where
  μ : Measure Ω
  primitives : PrimitiveTriple d Ω μ
  states : StatePresentation d S
  process : MarkovProcess S Ω
  common_law : ∀ x, process.law x = μ
  path : S → Ω → SixPath K J
  arrivals : S → Ω → ℝ≥0 → Fin K → ℕ
  departures : S → Ω → ℝ≥0 → Fin K → ℕ
  discipline : S → Fin K → ℝ≥0
  discipline_measurable : ∀ k, Measurable (fun x => discipline x k)
  discipline_without_old_rates : ∀ x y,
    (states.coordinates x).1.jobs = (states.coordinates y).1.jobs →
    (states.coordinates x).1.u = (states.coordinates y).1.u →
    (states.coordinates x).1.v = (states.coordinates y).1.v → discipline x = discipline y
  discipline_valid : ∀ x,
    ValidState d { (states.coordinates x).1 with r := discipline x }
  initial : ∀ x ω, PrimitiveGood primitives ω → process.X x 0 ω = x
  regular : ∀ x ω, PrimitiveGood primitives ω → FluidRegular (path x ω)
  cumulative_zero : ∀ x ω, PrimitiveGood primitives ω →
    (path x ω).A 0 = 0 ∧ (path x ω).D 0 = 0 ∧
    (path x ω).T 0 = 0 ∧ (path x ω).Y 0 = 0
  count_identification : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).A t k = arrivals x ω t k ∧
    (path x ω).D t k = departures x ω t k ∧
    (path x ω).Z t k = queueCount (states.coordinates (process.X x t ω)).1 k
  path_measurable : ∀ x t,
    Measurable (fun ω => (path x ω).A t) ∧ Measurable (fun ω => (path x ω).D t) ∧
    Measurable (fun ω => (path x ω).T t) ∧ Measurable (fun ω => (path x ω).W t) ∧
    Measurable (fun ω => (path x ω).Y t) ∧ Measurable (fun ω => (path x ω).Z t)
  path_right_continuous : ∀ x ω, PrimitiveGood primitives ω → ∀ t,
    ContinuousWithinAt (fun s => (path x ω).A s) (Set.Ici t) t ∧
    ContinuousWithinAt (fun s => (path x ω).D s) (Set.Ici t) t
  effort_continuous : ∀ x ω, PrimitiveGood primitives ω →
    Continuous (path x ω).T ∧ Continuous (path x ω).Y
  flow : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).Z t k = (path x ω).Z 0 k + (path x ω).A t k - (path x ω).D t k
  routing : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    arrivals x ω t k =
      (if h : k ∈ d.external then
        externalCount (primitives.xi ⟨k, h⟩) ((states.coordinates x).1.u k) t ω
        else 0) +
      ∑ l, routingCount primitives l k (departures x ω t l) ω
  workload : ∀ x ω, PrimitiveGood primitives ω → ∀ t j,
    (path x ω).W t j =
      (∑ k ∈ Finset.univ.filter (fun k => d.station k = j),
        (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
          ((states.coordinates x).1.v k)
          (queueCount (states.coordinates x).1 k + arrivals x ω t k) ω : ℝ)) -
      ∑ k ∈ Finset.univ.filter (fun k => d.station k = j), (path x ω).T t k
  station_effort : ∀ x ω, PrimitiveGood primitives ω → ∀ t j,
    (∑ k ∈ Finset.univ.filter (fun k => d.station k = j), (path x ω).T t k) +
      (path x ω).Y t j = t
  nonidling : ∀ x ω, PrimitiveGood primitives ω → ∀ j s t, s ≤ t →
    (path x ω).Y s j < (path x ω).Y t j →
      ∃ u ∈ Set.Icc s t, (path x ω).W u j = 0
  cumulative_service : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
      ((states.coordinates x).1.v k) (departures x ω t k) ω : ℝ) ≤ (path x ω).T t k
  residual_service : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    let st := (states.coordinates (process.X x t ω)).1
    if queueCount st k = 0 then
      (path x ω).T t k =
        (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
          ((states.coordinates x).1.v k) (departures x ω t k) ω : ℝ)
    else (st.v k : ℝ) =
      (serviceWork (primitives.gamma k) (queueCount (states.coordinates x).1 k)
        ((states.coordinates x).1.v k) (departures x ω t k + 1) ω : ℝ) - (path x ω).T t k
  residual_arrival : ∀ x ω, PrimitiveGood primitives ω → ∀ t
    (k : {k : Fin K // k ∈ d.external}),
    ((states.coordinates (process.X x t ω)).1.u k : ℝ) =
      ((states.coordinates x).1.u k : ℝ) +
      (renewalSum (primitives.xi k)
        (externalCount (primitives.xi k) ((states.coordinates x).1.u k) t ω) ω : ℝ) - t
  oldest_first : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (((states.coordinates (process.X x t ω)).1.jobs.filter (fun a => a.1 = k)).map
      Prod.snd) =
    (((((states.coordinates x).1.jobs.filter (fun a => a.1 = k)).map
      (fun a => a.2 + t)) ++
      (List.range (arrivals x ω t k)).map
        (fun n => arrivalAge (fun s => arrivals x ω s k) t (n + 1))).drop
          (departures x ω t k))
  service_allocation : ∀ x ω, PrimitiveGood primitives ω → ∀ t k,
    (path x ω).T t k = ∫ s : ℝ in (0 : ℝ)..(t : ℝ),
      ((states.coordinates (process.X x s.toNNReal ω)).1.r k : ℝ)
  constant_rates_between_events : ∀ x ω, PrimitiveGood primitives ω → ∀ s t,
    s ≤ t → arrivals x ω s = arrivals x ω t → departures x ω s = departures x ω t →
      (states.coordinates (process.X x s ω)).1.r =
      (states.coordinates (process.X x t ω)).1.r
  update_rates_at_events : ∀ x ω, PrimitiveGood primitives ω → ∀ t : ℝ≥0,
    0 < t → (∀ s < t, arrivals x ω s ≠ arrivals x ω t ∨
      departures x ω s ≠ departures x ω t) →
    (states.coordinates (process.X x t ω)).1.r = discipline (process.X x t ω)

noncomputable def HLNetwork.size (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  stateSize (n.states.coordinates x).1

noncomputable def HLNetwork.uMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  ∑ k, (n.states.coordinates x).1.u k

noncomputable def HLNetwork.vMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  ∑ k, (n.states.coordinates x).1.v k

noncomputable def HLNetwork.zMass (n : HLNetwork d S Ω) (x : S) : ℝ≥0 :=
  (n.states.coordinates x).1.jobs.length

end BramsonQueueing.Fluid

MODULE Def_BramsonQueueing_Fluid_FluidLimits
import Definitions.Def_BramsonQueueing_Fluid_HLNetwork

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace BramsonQueueing.Fluid

variable {K J : ℕ} {d : NetworkData K J} {S Ω : Type*}
  [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
  [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace Ω]

/-- (4.71): scaling diverges, initial queue mass is bounded after scaling,
and both residual masses vanish after scaling. -/
def AdmissibleScaling (n : HLNetwork d S Ω) (a : ℕ → ℝ≥0) (x : ℕ → S) : Prop :=
  (∀ i, 0 < a i) ∧ Tendsto a atTop atTop ∧
  (∃ B : ℝ, ∀ i, (n.zMass (x i) : ℝ) / a i ≤ B) ∧
  Tendsto (fun i => (n.uMass (x i) : ℝ) / a i) atTop (𝓝 0) ∧
  Tendsto (fun i => (n.vMass (x i) : ℝ) / a i) atTop (𝓝 0)

def IsFluidLimit (n : HLNetwork d S Ω) (q : SixPath K J) : Prop :=
  ∃ ω, PrimitiveGood n.primitives ω ∧ ∃ a x,
    AdmissibleScaling n a x ∧ SixUOC (fun i => scaleSix (a i) (n.path (x i) ω)) q

def FluidLimitsStable (n : HLNetwork d S Ω) : Prop := StableFamily (IsFluidLimit n)

/-- Association includes subsequence existence for every admissible sequence,
as required on printed p.112; it is not just a vacuous implication about limits. -/
def Associated (n : HLNetwork d S Ω) (model : FluidModel d) : Prop :=
  ∀ ω, PrimitiveGood n.primitives ω → ∀ a x, AdmissibleScaling n a x →
    ∃ r : ℕ → ℕ, StrictMono r ∧ ∃ q : SixPath K J,
      SixUOC (fun i => scaleSix (a (r i)) (n.path (x (r i)) ω)) q ∧ model.Solution q

/-- Convergence to zero as the full state size tends to infinity. -/
def VanishesAtLargeStates (n : HLNetwork d S Ω) (f : S → ℝ≥0∞) : Prop :=
  ∀ ε : ℝ≥0, 0 < ε → ∃ R : ℝ≥0, ∀ x, R ≤ n.size x → f x ≤ ε

/-- The complete residual-time conclusions (4.91)–(4.93), with a single c₀. -/
def ResidualConclusions (n : HLNetwork d S Ω) : Prop :=
  (∃ C : ℝ≥0, ∀ t : ℝ≥0, 1 ≤ t → ∀ x, n.size x ≤ t →
    (∫⁻ ω, (n.uMass (n.process.X x t ω) : ℝ≥0∞) ∂n.μ) / t ≤ C ∧
    (∫⁻ ω, (n.vMass (n.process.X x t ω) : ℝ≥0∞) ∂n.μ) / t ≤ C) ∧
  ∃ c₀ : ℝ≥0, 1 ≤ c₀ ∧ ∀ c ≥ c₀,
    (∀ ω, PrimitiveGood n.primitives ω →
      VanishesAtLargeStates n (fun x =>
        (n.uMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) / n.size x) ∧
      VanishesAtLargeStates n (fun x =>
        (n.vMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) / n.size x)) ∧
    VanishesAtLargeStates n (fun x =>
      (∫⁻ ω, (n.uMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) ∂n.μ) / n.size x) ∧
    VanishesAtLargeStates n (fun x =>
      (∫⁻ ω, (n.vMass (n.process.X x (c * n.size x) ω) : ℝ≥0∞) ∂n.μ) / n.size x)

end BramsonQueueing.Fluid
END VERBATIM DEPENDENCY CONTEXT -/
