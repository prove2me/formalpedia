-- Prove2me | Theorems.Thm_EntropyMFG_Enhanced_theorem_4
-- name    : EntropyMFG.Enhanced.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:26:08.830526+00:00
-- url     : https://prove2.me/theorems/a2aaf689-3176-4c1d-9b8f-26c180bdddbb
-- title:
--   Theorem 4 (MFG-EE): explicit enhanced-entropy Nash equilibrium
-- statement:
--   Let $0<T<\infty$, $t\in[0,T]$, and $A,B,D,Q,\bar Q,\lambda_{SE}>0$, $\lambda_{CE}\ge0$. Work on any filtered probability space satisfying the usual conditions with a standard Brownian motion $W$ relative to that filtration. The initial random variable $\xi$ is $\mathcal F_t$-measurable, independent of $W$, has a Lebesgue density law $\nu$, and has finite second moment. Put $m^*=\mathbb E\xi$ and $v_0=\mathbb E\xi^2-(\mathbb E\xi)^2$.
--
--   Use exactly the printed coefficients $\eta,\gamma,\kappa,K,M$ of (3.9)–(3.11) in the preceding definition, with fixed initial time $t$ and variance $v_0$, and set
--   $$\widetilde V(s,x)=-\tfrac12\eta_s(x-m^*)^2+\gamma_s,\qquad
--   \pi_s^*(u;x)=N\!\left(\frac{\lambda_{SE}+\lambda_{CE}}{\lambda_{SE}}\frac{B(m^*-x)}{D^2},\frac{\lambda_{SE}+\lambda_{CE}}{D^2\eta_s}\right)(u).$$
--   Then $\eta_s>0$ for every $s\in[0,T]$. There exist population state laws $\mu^*$, population action densities $\alpha^*$ and a controlled state process $X^*$ such that the displayed feedback is admissible for the original (MFG-EE), is a best response against **every** admissible deviation, and has finite payoff
--   $$V^*_{EE}(t)=\mathbb E_{\xi\sim\nu}[\widetilde V(t,\xi)],$$
--   equal to the actual supremum of admissible payoffs. The integrability of this quadratic expectation is part of the conclusion. The triple is a Nash equilibrium in Definition 1: $\mu_t^*=\nu$, $\mu_s^*=\mathrm{Law}(X_s^*)$, and $\alpha_s^*(u;x)=\pi_s^*(u;x)$ for every time, state and action.
--
--   Moreover the same controlled state is the unique strong solution, up to indistinguishability, of the printed equation
--   $$dX_s^*=\left(A+r\frac{B^2}{D^2}\right)(m^*-X_s^*)ds+D\sqrt{\left(A+r\frac{B^2}{D^2}\right)^2(X_s^*-m^*)^2+\frac{\lambda_{SE}+\lambda_{CE}}{D^2\eta_s}}\,dW_s,\quad X_t^*=\xi,$$
--   where $r=(\lambda_{SE}+\lambda_{CE})/\lambda_{SE}$. Finally, $X_s^*$ is integrable and $m_s^*=\mathbb E X_s^*=m^*$ for all $s\in[t,T]$. There is no assertion that the equilibrium itself is unique.
--
--   The source's diffusion mismatch and its printed $K$ are retained. Their numerical counterexamples and proof discrepancy are recorded separately as insights; no corrected statement replaces this goal.
--
--   Differences from the source:
--   - reading: the unstarred m in (3.13) → the fixed initial mean m*; reason: the surrounding theorem uses m* and concludes its constancy
--   - reading: F_t-progressively measurable in admissibility (ii) → progressively measurable relative to (F_s) on [t,T]; reason: the filtration-indexed stochastic-control convention in §2
--   - encoding: probability densities and their laws; equality of policies as measures → real Lebesgue densities and withDensity laws, with feedback measurability tested on Borel action sets; reason: density representatives are identified modulo null sets and no state or action is discretized
--   - encoding: usual filtered Brownian space and strong SDE solutions → finite-horizon increment laws and independence, a concrete local simple-approximation Itô relation, and uniqueness up to indistinguishability; reason: makes stochastic integration explicit with almost-sure pathwise square integrability and no extra expected moment bound
--   - encoding: defined entropy integrals, finite expected total payoff, and supremum over admissible policies → guarded signed extended integrals, real payoff witnesses, and an EReal supremum; zero cross weight omits that term; reason: prevents default-zero nonintegrable integrals and indeterminate infinity arithmetic without restricting deviations
--   - encoding: m*=E[ξ] and Var[ξ]=E[ξ²]-(E[ξ])² → moments of the given law ν, with κ carrying the fixed initial time separately; reason: HasLaw identifies these with expectations of ξ and preserves the initial law throughout γ
--   - encoding: integrals from a to b on the ordered time horizon → Lebesgue integrals over Icc a b; reason: endpoints have Lebesgue measure zero, including the zero-length terminal case
-- source:
--   Guo, Xu, Zariphopoulou, Entropy Regularization for Mean Field Games with Learning, arXiv:2010.00145v2, https://arxiv.org/abs/2010.00145v2, Theorem 4, pp. 10–11, (3.9)–(3.14); standing assumptions §2 pp. 3–6 and §3.2 pp. 9–10

import Definitions.Def_EntropyMFG_Enhanced_Explicit

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

/- DEPENDENCY SOURCE TRANSCRIPT BEGIN
-- Imported module: Definitions.Def_EntropyMFG_Enhanced_Density
import Mathlib

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

/-- Lebesgue probability densities, identified up to almost everywhere equality. -/
def IsDensity (p : ℝ → ℝ) : Prop :=
  Integrable p volume ∧ (∀ᵐ u ∂volume, 0 ≤ p u) ∧ ∫ u, p u = 1

def densityMeasure (p : ℝ → ℝ) : Measure ℝ :=
  volume.withDensity (fun u => ENNReal.ofReal (p u))

/-- Signed extended integral relation. The two infinite parts are never subtracted.
A finite output therefore certifies integrability, rather than a default zero. -/
def HasExtendedIntegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (f : E → EReal) (z : EReal) : Prop :=
  AEMeasurable f μ ∧
  let p := ∫⁻ x, (f x).toENNReal ∂μ
  let n := ∫⁻ x, (-f x).toENNReal ∂μ
  (p ≠ ⊤ ∨ n ≠ ⊤) ∧ z = (p : EReal) - (n : EReal)

/-- The extended logarithm, with log zero = minus infinity. -/
def logDensity (a : ℝ) : EReal := if 0 < a then (Real.log a : EReal) else ⊥

/-- Differential Shannon entropy, with the convention 0 log 0 = 0. -/
def HasShannonEntropy (p : ℝ → ℝ) (h : EReal) : Prop :=
  HasExtendedIntegral volume (fun u => (-(p u * Real.log (p u)) : ℝ)) h

/-- Average of log densities, followed by the action integral; not log of a mixture.
Zero action mass contributes zero even when the population log is infinite. -/
def HasCrossEntropy (p : ℝ → ℝ) (α : ℝ → ℝ → ℝ) (μ : Measure ℝ)
    (h : EReal) : Prop :=
  ∃ L : ℝ → EReal,
    (∀ᵐ u ∂(densityMeasure p),
      HasExtendedIntegral μ (fun y => logDensity (α y u)) (L u)) ∧
    HasExtendedIntegral (densityMeasure p) (fun u => -L u) h

/-- Excludes the indeterminate addition of opposite infinities. -/
def DefinedSum (a b : EReal) : Prop :=
  ¬ (a = ⊤ ∧ b = ⊥) ∧ ¬ (a = ⊥ ∧ b = ⊤)

end EntropyMFG.Enhanced

-- Imported module: Definitions.Def_EntropyMFG_Enhanced_Stochastic
import Definitions.Def_EntropyMFG_Enhanced_Density

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Progressiveness restricted to the indicated finite time interval. -/
def ProgressiveOn {E : Type*} [MeasurableSpace E]
    (F : Filtration ℝ mΩ) (t T : ℝ) (H : ℝ → Ω → E) : Prop :=
  ∀ s ∈ Icc t T,
    Measurable[Subtype.instMeasurableSpace.prod (F s)]
      (fun p : Icc t s × Ω => H p.1 p.2)

/-- Usual filtered Brownian probability space on [0,T]. The increment law uses variance,
not standard deviation; independence is relative to the supplied filtration. -/
def BrownianOn (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (T : ℝ) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ N : Set Ω, P N = 0 → MeasurableSet[F 0] N) ∧
  (∀ s ∈ Ico 0 T, F s = ⨅ u : {u : ℝ // s < u ∧ u ≤ T}, F u.val) ∧
  (∀ s ∈ Icc 0 T, Measurable[F s] (W s)) ∧
  (∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun s => W s ω) (Icc 0 T)) ∧
  (∀ r ∈ Icc 0 T, ∀ s ∈ Icc r T,
    HasLaw (fun ω => W s ω - W r ω) (gaussianReal 0 (Real.toNNReal (s-r))) P ∧
    Indep (MeasurableSpace.comap (fun ω => W s ω - W r ω) inferInstance) (F r) P)

/-- Predictable dyadic simple integrand on [t,s]. -/
def stepValue (t s : ℝ) (n : ℕ) (a : ℕ → Ω → ℝ) (z : ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2^n),
    if z ∈ Ioc (t + (s-t) * k / (2:ℝ)^n) (t + (s-t) * (k+1) / (2:ℝ)^n)
    then a k ω else 0

def stepSum (W : ℝ → Ω → ℝ) (t s : ℝ) (n : ℕ) (a : ℕ → Ω → ℝ)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (2^n), a k ω *
    (W (t + (s-t) * (k+1) / (2:ℝ)^n) ω - W (t + (s-t) * k / (2:ℝ)^n) ω)

/-- Local Brownian integral by bounded predictable simple approximations. Integrated
squared approximation error tends to zero in probability, not necessarily in expectation.
The integrand has finite energy almost surely; no all-samples or global L² condition. -/
def HasItoIntegral (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (H J : ℝ → Ω → ℝ) : Prop :=
  ProgressiveOn F t T H ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun z => H z ω ^ 2) (Icc t T)) ∧
  (∀ s ∈ Icc t T, Measurable[F s] (J s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => J s ω) (Icc t T)) ∧
  ∀ s ∈ Icc t T, ∃ a : ℕ → ℕ → Ω → ℝ,
    (∀ (n k : ℕ), k < 2^n → Measurable[F (t + (s-t) * k / (2:ℝ)^n)] (a n k)) ∧
    (∀ n, ∃ C : ℝ, ∀ k, k < 2^n → ∀ ω, |a n k ω| ≤ C) ∧
    TendstoInMeasure P
      (fun n ω => ∫ z in Icc t s, (stepValue t s n (a n) z ω - H z ω)^2)
      atTop (fun _ => (0 : ℝ)) ∧
    TendstoInMeasure P (fun n => stepSum W t s n (a n)) atTop (J s)

/-- Strong solution with the given Brownian motion and initial variable. -/
def StrongSolution (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (ξ : Ω → ℝ) (b σ : ℝ → Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ s ∈ Icc t T, Measurable[F s] (X s)) ∧
  (∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Icc t T)) ∧
  (∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω (X s ω)) (Icc t T)) ∧
  ∃ J : ℝ → Ω → ℝ,
    HasItoIntegral P F W t T (fun s ω => σ s ω (X s ω)) J ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t T,
      X s ω = ξ ω + (∫ z in Icc t s, b z ω (X z ω)) + J s ω

/-- Uniqueness is indistinguishability on the horizon, not pointwise equality. -/
def UniqueStrongSolution (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t T : ℝ) (ξ : Ω → ℝ) (b σ : ℝ → Ω → ℝ → ℝ) (X : ℝ → Ω → ℝ) : Prop :=
  StrongSolution P F W t T ξ b σ X ∧
  ∀ Y, StrongSolution P F W t T ξ b σ Y →
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t T, Y s ω = X s ω

end EntropyMFG.Enhanced

-- Imported module: Definitions.Def_EntropyMFG_Enhanced_Game
import Definitions.Def_EntropyMFG_Enhanced_Stochastic

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

structure Parameters where
  T : ℝ
  A : ℝ
  B : ℝ
  D : ℝ
  Q : ℝ
  Qbar : ℝ
  lambdaSE : ℝ
  lambdaCE : ℝ
  T_pos : 0 < T
  A_pos : 0 < A
  B_pos : 0 < B
  D_pos : 0 < D
  Q_pos : 0 < Q
  Qbar_pos : 0 < Qbar
  lambdaSE_pos : 0 < lambdaSE
  lambdaCE_nonneg : 0 ≤ lambdaCE

/-- Population densities and their finite first moments; no candidate mean is imposed. -/
def Population (t T : ℝ) (ν : Measure ℝ) (μ : ℝ → Measure ℝ)
    (α : ℝ → ℝ → ℝ → ℝ) : Prop :=
  μ t = ν ∧
  (∀ s ∈ Icc t T, (∃ ρ : ℝ → ℝ, IsDensity ρ ∧ μ s = densityMeasure ρ) ∧
    Integrable (fun x : ℝ => x) (μ s)) ∧
  (∀ s ∈ Icc t T, ∀ x, IsDensity (α s x))

def populationMean (μ : ℝ → Measure ℝ) (s : ℝ) : ℝ := ∫ x, x ∂(μ s)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Policy process: time, sample, action. No Gaussian restriction. -/
abbrev Policy (Ω : Type*) := ℝ → Ω → ℝ → ℝ

/-- Measurable density-valued Markov feedback, tested on every Borel action set. -/
def Feedback (t T : ℝ) (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  (∀ s ∈ Icc t T, ∀ x, IsDensity (f s x)) ∧
  ∀ Z : Set ℝ, MeasurableSet Z →
    Measurable (fun p : Icc t T × ℝ => densityMeasure (f p.1 p.2) Z)

def originalDrift (p : Parameters) (μ : ℝ → Measure ℝ) (π : Policy Ω)
    (s : ℝ) (ω : Ω) (x : ℝ) : ℝ :=
  ∫ u, (p.A * (populationMean μ s - x) + p.B * u) * π s ω u

def originalDiffusion (p : Parameters) (π : Policy Ω)
    (s : ℝ) (ω : Ω) (_x : ℝ) : ℝ :=
  p.D * Real.sqrt (∫ u, u^2 * π s ω u)

/-- The actual MFG-EE equation, with its action integrals defined almost everywhere. -/
def OriginalState (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ) (μ : ℝ → Measure ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) : Prop :=
  (∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Icc t p.T)),
    Integrable (fun u => u^2 * π s ω u) volume) ∧
  UniqueStrongSolution P F W t p.T ξ (originalDrift p μ π) (originalDiffusion p π) X

/-- Running reward with both entropy signs as printed. Cross entropy is absent at lambdaCE=0. -/
def RunningReward (p : Parameters) (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (s x : ℝ) (π : ℝ → ℝ) (r : EReal) : Prop :=
  ∃ hs hc : EReal, HasShannonEntropy π hs ∧
    (if p.lambdaCE = 0 then hc = 0 else HasCrossEntropy π (α s) (μ s) hc) ∧
    DefinedSum ((p.lambdaSE : EReal) * hs) ((p.lambdaCE : EReal) * hc) ∧
    r = ((-p.Q / 2 * (x - populationMean μ s)^2 : ℝ) : EReal) +
      (p.lambdaSE : EReal) * hs + (p.lambdaCE : EReal) * hc

/-- Finite total expected payoff. Integrability is imposed on the total realized reward,
not on each separate entropy term or on a fourth state moment. -/
def HasPayoff (p : Parameters) (P : Measure Ω) (t : ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  ∃ r : ℝ → Ω → EReal, ∃ R : Ω → ℝ,
    (∀ᵐ ω ∂P,
      (∀ᵐ s ∂(volume.restrict (Icc t p.T)),
        RunningReward p μ α s (X s ω) (π s ω) (r s ω)) ∧
      HasExtendedIntegral (volume.restrict (Icc t p.T)) (fun s => r s ω) (R ω)) ∧
    Integrable (fun ω => R ω - p.Qbar / 2 * (X p.T ω - populationMean μ p.T)^2) P ∧
    v = ∫ ω, R ω - p.Qbar / 2 * (X p.T ω - populationMean μ p.T)^2 ∂P

/-- All five clauses on p.5. Equality of policy measures holds simultaneously in time. -/
def Admissible (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ)
    (π : Policy Ω) (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  (∀ s ∈ Icc t p.T, ∀ᵐ ω ∂P, IsDensity (π s ω)) ∧
  (∀ Z : Set ℝ, MeasurableSet Z →
    ProgressiveOn F t p.T (fun s ω => densityMeasure (π s ω) Z)) ∧
  OriginalState p P F W t ξ μ π X ∧
  HasPayoff p P t μ α π X v ∧
  ∃ f : ℝ → ℝ → ℝ → ℝ, Feedback t p.T f ∧
    ∀ᵐ ω ∂P, ∀ s ∈ Icc t p.T,
      densityMeasure (π s ω) = densityMeasure (f s (X s ω))

/-- Actual supremum over all admissible policy processes, with state and payoff witnesses.
Empty and unbounded sets retain -infinity and +infinity respectively. -/
def gameValue (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ)
    (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ) : EReal :=
  sSup {z : EReal | ∃ π X v, Admissible p P F W t ξ μ α π X v ∧ z = (v : EReal)}

end EntropyMFG.Enhanced

-- Imported module: Definitions.Def_EntropyMFG_Enhanced_Equilibrium
import Definitions.Def_EntropyMFG_Enhanced_Game

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Definition 1: admissibility, best response against every admissible deviation,
and state/action consistency. The game value is attained. -/
def IsEquilibrium (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ)
    (W : ℝ → Ω → ℝ) (t : ℝ) (ξ : Ω → ℝ) (ν : Measure ℝ)
    (μ : ℝ → Measure ℝ) (α f : ℝ → ℝ → ℝ → ℝ)
    (X : ℝ → Ω → ℝ) (v : ℝ) : Prop :=
  Population t p.T ν μ α ∧ Feedback t p.T f ∧
  Admissible p P F W t ξ μ α (fun s ω => f s (X s ω)) X v ∧
  (∀ π Y w, Admissible p P F W t ξ μ α π Y w → w ≤ v) ∧
  (∀ s ∈ Icc t p.T, ∀ x u, α s x u = f s x u) ∧
  (∀ s ∈ Icc t p.T, μ s = Measure.map (X s) P) ∧
  gameValue p P F W t ξ μ α = (v : EReal)

end EntropyMFG.Enhanced

-- Imported module: Definitions.Def_EntropyMFG_Enhanced_Explicit
import Definitions.Def_EntropyMFG_Enhanced_Equilibrium

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section

namespace EntropyMFG.Enhanced

def ratio (p : Parameters) : ℝ := (p.lambdaSE + p.lambdaCE) / p.lambdaSE

def eta (p : Parameters) (s : ℝ) : ℝ :=
  let c := 2*p.A + p.B^2 / p.D^2 * ratio p
  p.Qbar * Real.exp (-c * (p.T-s)) + p.Q / c * (1 - Real.exp (-c * (p.T-s)))

/-- The printed K, including its multiplication of A by the entropy ratio. -/
def printedK (p : Parameters) : ℝ := -(p.A + p.B^2 / p.D^2) * ratio p

def printedM (p : Parameters) : ℝ := (p.B / p.D * ratio p)^2

/-- Start time t and initial variance v0 remain fixed as s varies. -/
def kappa (p : Parameters) (t v0 s : ℝ) : ℝ :=
  Real.exp ((2*printedK p + printedM p) * (s-t)) * v0 +
    ∫ z in Icc t s, Real.exp ((printedM p + 2*printedK p) * (s-z)) *
      (p.lambdaSE + p.lambdaCE) / eta p z

def gamma (p : Parameters) (t v0 s : ℝ) : ℝ :=
  (p.lambdaSE+p.lambdaCE)/2 * Real.log (2*Real.pi*(p.lambdaSE+p.lambdaCE)/p.D^2) * (p.T-s) -
  (p.lambdaSE+p.lambdaCE)/2 * (∫ z in Icc s p.T, Real.log (eta p z)) +
  p.B^2/(2*p.D^2) * (p.lambdaCE*(p.lambdaSE+p.lambdaCE)/p.lambdaSE^2) *
    (∫ z in Icc s p.T, eta p z * kappa p t v0 z)

def quadraticValue (p : Parameters) (t m v0 s x : ℝ) : ℝ :=
  -eta p s / 2 * (x-m)^2 + gamma p t v0 s

/-- Normal density with mean a and variance v. Uses are at strictly positive v. -/
def normalDensity (a v u : ℝ) : ℝ :=
  Real.exp (-(u-a)^2 / (2*v)) / Real.sqrt (2*Real.pi*v)

def candidatePolicy (p : Parameters) (m s x u : ℝ) : ℝ :=
  normalDensity (ratio p * p.B * (m-x) / p.D^2)
    ((p.lambdaSE+p.lambdaCE)/(p.D^2*eta p s)) u

/-- The printed equation (3.13), separate from the original model equation. -/
def printedDrift (p : Parameters) (m _s x : ℝ) : ℝ :=
  (p.A + ratio p * p.B^2 / p.D^2) * (m-x)

def printedDiffusion (p : Parameters) (m s x : ℝ) : ℝ :=
  p.D * Real.sqrt ((p.A + ratio p * p.B^2 / p.D^2)^2 * (x-m)^2 +
    (p.lambdaSE+p.lambdaCE)/(p.D^2*eta p s))

end EntropyMFG.Enhanced
DEPENDENCY SOURCE TRANSCRIPT END -/

namespace EntropyMFG.Enhanced

/-- Full equilibrium, value, controlled state and mean assertion. -/
theorem theorem_4 {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (p : Parameters) (P : Measure Ω) (F : Filtration ℝ mΩ) (W : ℝ → Ω → ℝ)
    (t : ℝ) (ht : t ∈ Icc 0 p.T) (hW : BrownianOn P F W p.T)
    (ξ : Ω → ℝ) (ν : Measure ℝ)
    (hξ : Measurable[F t] ξ)
    (hind : IndepFun ξ (fun ω (s : Icc (0:ℝ) p.T) => W s ω) P)
    (hlaw : HasLaw ξ ν P)
    (hν : ∃ ρ : ℝ → ℝ, IsDensity ρ ∧ ν = densityMeasure ρ)
    (hsecond : Integrable (fun x : ℝ => x^2) ν) :
    let m := ∫ x, x ∂ν
    let v0 := (∫ x, x^2 ∂ν) - m^2
    (∀ s ∈ Icc 0 p.T, 0 < eta p s) ∧
    ∃ (μ : ℝ → Measure ℝ) (α : ℝ → ℝ → ℝ → ℝ) (X : ℝ → Ω → ℝ),
      Integrable (fun x => quadraticValue p t m v0 t x) ν ∧
      IsEquilibrium p P F W t ξ ν μ α (candidatePolicy p m) X
        (∫ x, quadraticValue p t m v0 t x ∂ν) ∧
      UniqueStrongSolution P F W t p.T ξ
        (fun s _ x => printedDrift p m s x)
        (fun s _ x => printedDiffusion p m s x) X ∧
      (∀ s ∈ Icc t p.T, Integrable (X s) P ∧
        populationMean μ s = m ∧ (∫ ω, X s ω ∂P) = m) := by sorry

end EntropyMFG.Enhanced
