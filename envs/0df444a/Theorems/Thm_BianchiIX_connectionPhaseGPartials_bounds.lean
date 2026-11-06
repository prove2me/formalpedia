-- Prove2me | Theorems.Thm_BianchiIX_connectionPhaseGPartials_bounds
-- name    : BianchiIX.connectionPhaseGPartials_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T09:52:20.901861+00:00
-- url     : https://prove2.me/theorems/78545c30-0a5b-435a-b938-498aaea58ff0
-- title:
--   The phase row retains its small wall factors
-- statement:
--   For $y=(m,u,v,w)\in\mathbb R^4$, define
--   $$K(u,v,w)=u^2+v^2+w^2-2(uv+vw+wu),\qquad \kappa=u(v+w-u),$$
--   $$F_m=-v^2+w^2+u(v-w)-m\kappa,\qquad
--   F_u=\tfrac12(1-m^2-(v-w)^2+u^2)u,$$
--   $$F_v=(m-1-\kappa)v,\qquad F_w=(-m-1-\kappa)w,\qquad
--   F=(F_m,F_u,F_v,F_w),$$
--   and $E(m,v)=(m-1)^2+v^2$.
--
--   Put $c=u(v+w-u)$, $s(m,u,v,w)=m-1-c$,
--   $b(m,u,v,w)=(1-m^2-(v-w)^2+u^2)/2$,
--   $D(m,u,v,w)=3+m^2+K(u,v,w)$, and $r(m,v)=\sqrt{(m-1)^2+v^2}$.
--
--   Assume $\mu\geq4$, $|m-\mu|\leq1/2$, $0\leq u\leq1/10000$,
--   and $0\leq v,w\leq1$.
--
--   For the positive reflected phase variable $m$, put
--   $$n(a,b)=\sqrt{a^2+b^2},\quad j(a,b)=\frac1{n(a,b)(n(a,b)+a)},$$
--   $$\phi=n(m+1,v)+n(m-1,w)-m,\quad
--   h=\frac{m+1}{n(m+1,v)}+\frac{m-1}{n(m-1,w)}-1,$$
--   $$Q=mh+\frac{v^2}{n(m+1,v)}+\frac{w^2}{n(m-1,w)},\quad
--   k=j(m+1,v)-j(m-1,w).$$
--   Write $\kappa=u(v+w-u)$, $s=m-1-\kappa$,
--   $b=(1-m^2-(v-w)^2+u^2)/2$, and
--   $$M_v=-\frac{v^2}{n(m+1,v)h},\qquad M_w=-\frac{w^2}{n(m-1,w)h}.$$
--   The four coordinate differential operators, in the order
--   $(\phi,\log u,\log v,\log w)$, are
--   $$L_0=h^{-1}\partial_m,\quad L_1=u\partial_u,\quad
--   L_2=M_v\partial_m+v\partial_v,\quad L_3=M_w\partial_m+w\partial_w.$$
--   Subscripts $i$ below denote the rational expressions obtained by these
--   rules, with total real-field division. On the regular positive-wall
--   region they are the corresponding coordinate partial derivatives. Set
--   $$N=h(v-w)+(v+w-u)Q,\quad R=h(v-w)+(v+w-u)(Q-s),$$
--   $$A=-N/s,\quad B=k/s,\quad G=uA+(vw)^2B,\quad
--   \alpha=b/s,\quad \beta=-1-2(1+\kappa)/s.$$
--   The coefficient matrix $C$ has rows $(G_i)_i$, $(\alpha_i)_i$ and
--   $(\beta_i)_i$.
--
--   The four phase coefficients satisfy
--   $$|G_0|\leq64(u/\mu^2+(vw)^2/\mu^4),\quad |G_1|\leq32u,$$
--   $$|G_2|\leq32(uv+(vw)^2/\mu^3),\quad
--   |G_3|\leq32(uw+(vw)^2/\mu^3).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/ConnectionPhaseWallBounds.lean#L8-L77

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_ConnectionBounds
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeighted
import Definitions.Def_BianchiIX_Analysis_ConnectionAmplitudeDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingKernelVariation
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseKernel
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeight
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseDirection
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWallDifferential
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseNumerator
import Definitions.Def_BianchiIX_Analysis_ConnectionPhaseLinearization
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open BianchiIX

theorem BianchiIX.connectionPhaseGPartials_bounds {μ m u v w : ℝ} (hμ : 4 ≤ μ)
    (hm : |m - μ| ≤ 1 / 2) (hu : 0 ≤ u ∧ u ≤ 1 / 10000)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : 0 ≤ w ∧ w ≤ 1) :
    |connectionPhaseGPartials m u v w 0| ≤ 64 * (u / μ ^ 2 + (v * w) ^ 2 / μ ^ 4) ∧
    |connectionPhaseGPartials m u v w 1| ≤ 32 * u ∧
    |connectionPhaseGPartials m u v w 2| ≤ 32 * (u * v + (v * w) ^ 2 / μ ^ 3) ∧
    |connectionPhaseGPartials m u v w 3| ≤ 32 * (u * w + (v * w) ^ 2 / μ ^ 3) := by sorry
