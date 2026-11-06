-- Prove2me | Theorems.Thm_BianchiIX_exists_common_borel_era_orbit
-- name    : BianchiIX.exists_common_borel_era_orbit
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T05:20:25.442729+00:00
-- url     : https://prove2.me/theorems/6a900d61-b923-4fd9-adc2-980f859781b2
-- title:
--   A jointly measurable statistical era orbit with unbounded physical times
-- statement:
--   The flow is the normalized vacuum Bianchi IX Einstein
--   flow with zero cosmological constant; $\mathcal X$ is its positive-wall,
--   constraint-one phase space. Assume the pointwise Birkhoff theorem for
--   ergodic probability-preserving maps on the real line and integrable
--   real observables. Assume also the Brehm attractor input:
--   off the Taub subspaces in $\mathcal X$ every distinct wall pair has
--   $2\sqrt{|N_iN_j|}\to0$ along the forward orbit.
--   A common exception is a Borel $N\subset\mathcal X$
--   containing the physical Taub subspaces and the physical orbits
--   eventually uniformly separated from all three Taub points; membership
--   is invariant at every existing flow time. Its pullback is Lebesgue
--   null on each transverse $C^1$ physical chart with open domain and
--   nonzero flux. Four-coordinate nullity means that every differentiable
--   map from the ambient state space to $\mathbb R^4$ sends $N$ to a
--   four-dimensional Lebesgue null set.
--   There exists $0<\delta\le1/40000$ such that
--   for each $0<\eta\le\delta$, integer $J\ge20$, $0<\sigma<1$,
--   $2J\sigma<1$, the conclusion holds.
--   For an era digit sequence $K_n$ and phases $y_n$ the
--   statistics are the following simultaneous limits. Every continuous
--   observable on $[0,1]$ has empirical mean equal in the limit to its
--   integral against $dy/((1+y)\log 2)$. Every finite positive digit
--   word has frequency equal to the Gauss measure of its cylinder. For
--   $k\ge1$ the digit and tail frequencies are
--   $\log_2((k+1)^2/(k(k+2)))$ and $\log_2(1+1/k)$. The mean of
--   $\min(K_n,R)$ tends to $\log_2(R+1)$ for each natural $R$, and the
--   untruncated mean tends to infinity.
--
--   There exist a cap in $(0,1)$, a common four-coordinate null exception,
--   a measurable ambient restart map and a measurable survivor choice on
--   $\mathcal X\setminus N$ with the chosen restart budget and state.
--   The digits, code, states, phases, physical times and frames are
--   measurable. The statistics hold both from the first state and after
--   its removal. Each digit is the floor of half the radius; each block
--   has the exact event itinerary, ends at the next entrance in the
--   appropriate frame, and starts at a positive existing physical time.
--   These times increase strictly to infinity.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/CommonEraOrbit.lean#L14-L88

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_Statistics_GaussCylinders
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Statistics_GaussMeasure
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Statistics_ObservableTransfer
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_EraCodingData
import Definitions.Def_BianchiIX_PhysicalEraData
import Definitions.Def_BianchiIX_GeometricExceptionData
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.List.Induction
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.Compact
import Mathlib.MeasureTheory.MeasurableSpace.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.ByContra
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Order.Interval.Set.Monotone

noncomputable section
open BianchiIX
open Set MeasureTheory Filter
open scoped Topology

theorem BianchiIX.exists_common_borel_era_orbit
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧
          ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
            geometricException ⊆ N ∧
            (∀ x : NormalizedState, ∀ t ∈ normalizedMaxDomain x 0,
              normalizedMaxCurve x 0 t ∈ N ↔ x ∈ N) ∧
            (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
              IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
              (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
              (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
              volume (U ∩ C ⁻¹' N) = 0) ∧ NullInFourCoordinates N ∧
            ∃ W : NormalizedState → CoreRestartData, Measurable W ∧
              ∃ p : ↥(physicalPhaseSpace \ N) → eraSurvivorDomain η J σ Bcap,
                Measurable p ∧ Measurable (EraSurvivor.digits ∘ p) ∧
                Measurable (EraSurvivor.code ∘ p) ∧ Measurable (EraSurvivor.state ∘ p) ∧
                Measurable (EraSurvivor.phase ∘ p) ∧
                Measurable (fun x => EraSurvivor.physicalTime (W x.val) (p x)) ∧
                Measurable (fun x => EraSurvivor.physicalFrame (W x.val) (p x)) ∧ ∀ x,
                  (p x).val = (W x.val).2 ∧ EraStatistics (EraSurvivor.digits (p x)) (EraSurvivor.phase (p x)) ∧
                  EraStatistics (shiftDigits (EraSurvivor.digits (p x)) 1)
                    (fun n => EraSurvivor.phase (p x) (1 + n)) ∧
                  (∀ n, Nat.floor (EraSurvivor.state (p x) n 0 / 2) = (EraSurvivor.digits (p x) n : ℕ)) ∧
                  StrictMono (EraSurvivor.physicalTime (W x.val) (p x)) ∧
                  Tendsto (EraSurvivor.physicalTime (W x.val) (p x)) atTop atTop ∧ ∀ n,
                    EraEventItinerary η J (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n) ∧
                    coreRadiusEntry (EraSurvivor.state (p x) (n + 1)) = terminalNaturalState η J
                      (eraCoreExit (EraSurvivor.digits (p x) n).natPred (EraSurvivor.state (p x) n)) ∧
                    0 < EraSurvivor.physicalTime (W x.val) (p x) n ∧
                    EraSurvivor.physicalTime (W x.val) (p x) n ∈ normalizedMaxDomain x.val 0 ∧
                    fromProjectiveState (coreRadiusEntry (EraSurvivor.state (p x) n)) =
                      (axisFrame (EraSurvivor.physicalFrame (W x.val) (p x) n)).map
                        (normalizedMaxCurve x.val 0 (EraSurvivor.physicalTime (W x.val) (p x) n)) := by sorry
