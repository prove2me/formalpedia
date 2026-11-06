-- Prove2me | Theorems.Thm_BianchiIX_exists_restartRadialFailure_partition
-- name    : BianchiIX.exists_restartRadialFailure_partition
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T05:09:38.734437+00:00
-- url     : https://prove2.me/theorems/c6e61120-a0d2-4cac-879f-f1f4f4c462f2
-- title:
--   An exact countable flux identity for the statistical radial exception
-- statement:
--   Assume the pointwise Birkhoff theorem on the real
--   line for every ergodic probability-preserving map and integrable real
--   observable. There exists $0<\delta\le1/40000$; for each
--   $0<\eta\le\delta$, integer $J\ge20$, $0<\sigma<1$ with $2J\sigma<1$,
--   the following choices can be made.
--   Choose a budget cap in $(0,1)$ and $0<h_*\le1/8$.
--   Fix $0<h\le h_*$, $q>3$, $D>4$, $P>6D+2$, $0<\epsilon\le1/128$.
--   For sufficiently small section width $0<d\le d_*\le h/8$ partition
--   the open section into angular and signed shear pieces at dyadic radii.
--   Each piece's bad parameters $F_i$ have unselected labels or an actual
--   return outside the typical survivor set. Let $E$ be their physical
--   images together with the dyadic boundary. Write $I_i$ for the integral
--   of the original flux density on the bad fibers, with Jacobian
--   $1/\zeta$ in angular coordinates or $1/(n_2 n_3)$ in shear coordinates.
--   All $F_i$ and $E$ are Borel and
--   $\mu_h^{\rm orig}(E)=\sum_i I_i$. Each point of the open section
--   outside $E$ has a piece whose actual output belongs to the typical
--   survivor domain; every successful parameter in a piece supplies a
--   survivor with that output and the era statistics.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Measure/RestartRadialPartition.lean#L98-L193

import Definitions.Def_BianchiIX_Literature
import Definitions.Def_BianchiIX_Dynamics_AxisMaps
import Definitions.Def_BianchiIX_AxisAndOrbitData
import Definitions.Def_BianchiIX_Statistics_EraStatistics
import Definitions.Def_BianchiIX_RadialFailureData
import Definitions.Def_BianchiIX_EraCodingData
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

noncomputable section
open BianchiIX
open Set MeasureTheory
open scoped ENNReal

theorem BianchiIX.exists_restartRadialFailure_partition (hBirkhoff : Literature.BirkhoffErgodicInput ℝ) :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 40000 ∧ ∀ η : ℝ, 0 < η → η ≤ δ →
      ∀ J : ℕ, 20 ≤ J → ∀ σ : ℝ, 0 < σ → σ < 1 → σ * (2 * J : ℕ) < 1 →
        ∃ Bcap > (0 : ℝ), Bcap < 1 ∧ ∃ hstar > (0 : ℝ), hstar ≤ 1 / 8 ∧
          ∀ h ∈ Ioc (0 : ℝ) hstar, ∀ q D P : ℝ, 3 < q → 4 < D → 6 * D + 2 < P →
            ∀ ε ∈ Ioc (0 : ℝ) (1 / 128), ∃ dstar > (0 : ℝ), dstar ≤ h / 8 ∧
              ∀ d ∈ Ioc (0 : ℝ) dstar,
                let F := restartRadialFailureFamily h q d ε P η J σ Bcap
                (∀ i, MeasurableSet (F i)) ∧ MeasurableSet (radialFailureSet d ε F) ∧
                  mainWallOriginalMeasure h (radialFailureSet d ε F) = (∑' i, radialFailureIntegral h d ε F i) ∧
                    (∀ z ∈ mainWallOpenSection d \ radialFailureSet d ε F,
                      ∃ i : RadialPieceIndex, z ∈ physicalRadialPiece d ε i ∧
                        restartRadialOutput h q d ε i (radialPieceInverse i.1 z) ∈
                          EraSurvivor.typicalDomain η J σ Bcap) ∧
                    ∀ i z, z ∈ radialPieceDomain d ε i → z ∉ F i →
                      ∃ p : eraSurvivorDomain η J σ Bcap,
                        p.val = restartRadialOutput h q d ε i z ∧
                        EraStatistics (EraSurvivor.digits p) (EraSurvivor.phase p) := by sorry
