-- Prove2me | Theorems.Thm_BianchiIX_exists_full_measure_era_statistics
-- name    : BianchiIX.exists_full_measure_era_statistics
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T05:24:32.036526+00:00
-- url     : https://prove2.me/theorems/f86f5785-a28b-4888-9924-3a3c29261a4d
-- title:
--   Full-measure era statistics for the exact vacuum Bianchi IX flow
-- statement:
--   The flow is the normalized vacuum Bianchi IX Einstein
--   flow with zero cosmological constant; $\mathcal X$ is its positive-wall,
--   constraint-one phase space. Assume the pointwise Birkhoff theorem for
--   ergodic probability-preserving maps on the real line and integrable
--   real observables. Assume also the Brehm attractor input:
--   off the Taub subspaces in $\mathcal X$ every distinct wall pair has
--   $2\sqrt{|N_iN_j|}\to0$ along the forward orbit.
--   For an era digit sequence $K_n$ and phases $y_n$ the
--   statistics are the following simultaneous limits. Every continuous
--   observable on $[0,1]$ has empirical mean equal in the limit to its
--   integral against $dy/((1+y)\log 2)$. Every finite positive digit
--   word has frequency equal to the Gauss measure of its cylinder. For
--   $k\ge1$ the digit and tail frequencies are
--   $\log_2((k+1)^2/(k(k+2)))$ and $\log_2(1+1/k)$. The mean of
--   $\min(K_n,R)$ tends to $\log_2(R+1)$ for each natural $R$, and the
--   untruncated mean tends to infinity.
--   There exist $0<\eta\le1/40000$
--   and a flow-invariant Borel set $N\subset\mathcal X$ containing the
--   physical Taub subspaces and the physical states eventually uniformly
--   separated from all three Taub points. Its pullback has measure zero
--   for every density with respect to Lebesgue measure in each of the
--   following charts: a physical $C^1$ three-coordinate chart on an open
--   domain with nonzero section flux, or a four-coordinate parametrization
--   that is $C^1$ on its domain with nonvanishing constraint volume form.
--   On $\mathcal X\setminus N$ there are measurable sequences of digits
--   $K_n$, core states $Y_n$, times $t_n$ and frames $A_n$ giving complete
--   physical eras with parameters $(\eta,45)$ and the statistics above.
--   For $z=\Pi(A_n\Phi_{t_n}x)$, $z_2=1$ and
--   $$R_n=(Y_n)_0=\sqrt{(z_0-1)^2+1},\qquad
--   R_n/2>1,\quad y_n=2/R_n\in(0,1),\quad K_n=\lfloor R_n/2\rfloor.$$
--   The times are positive and increase strictly to infinity; the states
--   are the actual consecutive framed entrances on this orbit.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/FullMeasureStatistics.lean#L13-L50

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Statistics_GaussCoding
import Definitions.Def_BianchiIX_AxisSectionMeasureData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Dynamics_SectionFlux
import Definitions.Def_BianchiIX_Dynamics_AxisSymmetry
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
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.exists_full_measure_era_statistics
    (hBirkhoff : Literature.BirkhoffErgodicInput ℝ)
    (hBrehm : Literature.BrehmIXAttractorInput) :
    ∃ η ∈ Ioc (0 : ℝ) (1 / 40000),
      ∃ N : Set NormalizedState, MeasurableSet N ∧ N ⊆ physicalPhaseSpace ∧
        geometricException ⊆ N ∧
        (∀ x : NormalizedState, ∀ s ∈ normalizedMaxDomain x 0,
          normalizedMaxCurve x 0 s ∈ N ↔ x ∈ N) ∧
        (∀ (C : SectionCoordinates → NormalizedState) (U : Set SectionCoordinates),
          IsOpen U → (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
          (∀ y ∈ U, positiveWalls (C y)) → (∀ y ∈ U, stateConstraint (C y) = 1) →
          (∀ y ∈ U, normalizedSectionFlux (C y) (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
          ∀ ρ : SectionCoordinates → ℝ≥0∞, (volume.withDensity ρ) (U ∩ C ⁻¹' N) = 0) ∧
        (∀ (C : FourCoordinates → NormalizedState) (U : Set FourCoordinates),
          (∀ y ∈ U, ContDiffAt ℝ 1 C y) →
          (∀ y ∈ U, normalizedConstraintVolume (C y)
            (fun i => fderiv ℝ C y (Pi.single i 1)) ≠ 0) →
          ∀ ρ : FourCoordinates → ℝ≥0∞, (volume.withDensity ρ) (U ∩ C ⁻¹' N) = 0) ∧
        ∃ K : ↥(physicalPhaseSpace \ N) → ℕ → ℕ+, Measurable K ∧
        ∃ Y : ↥(physicalPhaseSpace \ N) → ℕ → CoreAngleState, Measurable Y ∧
        ∃ t : ↥(physicalPhaseSpace \ N) → ℕ → ℝ, Measurable t ∧
        ∃ a : ↥(physicalPhaseSpace \ N) → ℕ → Fin 6, Measurable a ∧
          ∀ x, PhysicalEraSequence η 45 x.val (K x) (Y x) (t x) (a x) ∧
            ∀ n, let z := toProjectiveState ((axisFrame (a x n)).map
                (normalizedMaxCurve x.val 0 (t x n)))
              z 2 = 1 ∧ Real.sqrt ((z 0 - 1) ^ 2 + 1) = Y x n 0 ∧
                1 < Y x n 0 / 2 ∧ 2 / Y x n 0 ∈ Ioo (0 : ℝ) 1 ∧
                (K x n : ℕ) = Nat.floor (Y x n 0 / 2) := by sorry
