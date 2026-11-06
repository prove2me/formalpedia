-- Prove2me | Theorems.Thm_BianchiIX_matchingPhase_auxiliary_m_bounds
-- name    : BianchiIX.matchingPhase_auxiliary_m_bounds
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T09:34:23.631658+00:00
-- url     : https://prove2.me/theorems/91e389af-8212-45d5-ba90-2dcd20b46663
-- title:
--   Ordinary phase derivatives of the matching slope and weight are small
-- statement:
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
--   For $\mu\geq4$ and $|m-\mu|\leq1/2$, with arbitrary real $v,w$,
--   $$0\leq h_m\leq\frac{9(v^2+w^2)}{2\mu^3},\qquad
--   |Q_m-1|\leq\frac{3(v^2+w^2)}{\mu^2}.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/MatchingPhaseAuxiliaryBounds.lean#L7-L65

import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Analysis_MatchingKernelDifferential
import Definitions.Def_BianchiIX_Analysis_MatchingPhaseWeightDifferential
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

theorem BianchiIX.matchingPhase_auxiliary_m_bounds {μ m v w : ℝ} (hμ : 4 ≤ μ) (hm : |m - μ| ≤ 1 / 2) :
    0 ≤ matchingPhaseSlopeDm m v w ∧
    matchingPhaseSlopeDm m v w ≤ 9 * (v ^ 2 + w ^ 2) / (2 * μ ^ 3) ∧
    |matchingPhaseWeightDm m v w - 1| ≤ 3 * (v ^ 2 + w ^ 2) / μ ^ 2 := by sorry
