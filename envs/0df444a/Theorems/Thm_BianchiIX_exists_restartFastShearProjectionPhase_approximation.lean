-- Prove2me | Theorems.Thm_BianchiIX_exists_restartFastShearProjectionPhase_approximation
-- name    : BianchiIX.exists_restartFastShearProjectionPhase_approximation
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-06T04:47:05.571117+00:00
-- url     : https://prove2.me/theorems/b4a8c038-b90a-4531-9891-6dad909a198f
-- title:
--   Reference phase and radial slope on both signed shear annuli
-- statement:
--   Write $\Phi_t x$ for the normalized vacuum Bianchi IX flow and
--   $x_h(Z)$ for the constraint-one, negative-first-shear chart with primary
--   wall $h$ and center coordinates $Z=(v,b,c)$ (second shear and the other
--   two walls). At time $t$, denote its primary wall by $n_t$ and center by
--   $Z_t$. Set $r(Z)=\sqrt{v^2+(b-c)^2}$. For $u=\sqrt{1-h^2}$ define
--   $A=3/(2+u)$, $B=3\sqrt3 h/(2+u)^2$, $H=9(1+u)/(2(2+u)^2)$,
--   $Q_h(v,w)=(Av+Bw)^2+H^2w^2$ and $F_h(Z)=\sqrt{Q_h(v,b-c)}/\sqrt3$.
--   On a shear annulus take $0<a$, $\rho\in[a,2a]$,
--   $Z=(\rho,n_2,n_3)$, $s=(q/2)\log(1/a)$, $Y=\Pi\Phi_s x_h(Z)$,
--   $k=\sqrt{(Y_0-1)^2+Y_2^2}$ and $F=F_h(Z)$. A signed annulus uses
--   $Z=(\omega\rho,n_2,n_3)$, $|\omega|=1$. Here $h>0$ is sufficiently
--   small and $a>0$ is sufficiently small thereafter. Primes are ordinary
--   radial derivatives with labels and cutoff fixed.
--   For small $h$ fix $C>0$ before choosing $q,P>2$.
--   If $0\le\epsilon\le1/64$, $0\le n_i\le2\epsilon a$, $n_3\le a^P$,
--   the cutoff exists with positive height for either shear sign. Let $f$
--   be the projected reciprocal core phase there. The phase $f$ is differentiable, with
--   $|f-F|\le C a^2$, $|f'-F'|\le Ca$, and
--   $1/(4\sqrt3)\le f'\le2/\sqrt3+1$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/ShearRestartFastPhaseComparison.lean#L11-L92

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_RadialTransportData
import Definitions.Def_BianchiIX_ShearTransportData
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

theorem BianchiIX.exists_restartFastShearProjectionPhase_approximation :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∃ K > (0 : ℝ), ∀ q P : ℝ, 2 < q → 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε σ n₂ n₃ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 64) → |σ| = 1 →
            (0 ≤ n₂ ∧ n₂ ≤ 2 * ε * a) → (0 ≤ n₃ ∧ n₃ ≤ 2 * ε * a) → n₃ ≤ a ^ P →
            ∀ ρ ∈ Icc a (2 * a),
              let T := q / 2 * Real.log (1 / a)
              T ∈ normalizedMaxDomain (restartSectionChart h (restartShearCurve σ n₂ n₃ ρ)) 0 ∧
              0 < restartFastShearHeight h T σ n₂ n₃ ρ ∧
              DifferentiableAt ℝ (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              |restartFastShearProjectionPhase h T σ n₂ n₃ ρ -
                restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ ρ)| ≤ K * a ^ 2 ∧
              |deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ -
                deriv (fun t => restartReferenceRadialPhase h (restartShearCurve σ n₂ n₃ t)) ρ| ≤ K * a ∧
              1 / (4 * Real.sqrt 3) ≤ deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ∧
              deriv (restartFastShearProjectionPhase h T σ n₂ n₃) ρ ≤ 2 / Real.sqrt 3 + 1 := by sorry
