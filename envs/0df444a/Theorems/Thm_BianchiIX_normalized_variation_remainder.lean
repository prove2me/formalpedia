-- Prove2me | Theorems.Thm_BianchiIX_normalized_variation_remainder
-- name    : BianchiIX.normalized_variation_remainder
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T22:20:52.08548+00:00
-- url     : https://prove2.me/theorems/6966a104-9770-4ce7-9c60-e53b4054e4c6
-- title:
--   The quadratic error between two solutions and their linear variation
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   Let $X=\mathbb R^5$ with coordinates $x=(p,s,a,b,c)$ and the sup norm. Write
--   $$F(x)=(P,Q,r_1a,r_2b,r_3c),\qquad \mathcal C(x)=C(p,s,a,b,c),$$
--   and let $W=\{(p,s,a,b,c)\in X:a>0,\ b>0,\ c>0\}$.
--
--   Write $N_1(x)=a$, $N_2(x)=b$, and $N_3(x)=c$. For initial data $(x_0,t_0)$,
--   let $I_{\max}(x_0,t_0)$ be the union of all open convex domains of solutions
--   with these initial data, and let $\alpha_{x_0,t_0}$ be their compatible curve.
--   A solution $S$ has such a domain $I_S$, a curve $\alpha_S$, and
--   $\alpha_S(t_0)=x_0$.
--
--   Let $\mathcal L(X,X)$ be the continuous linear operators on $X$ and set
--   $$A(x)=dF_x,\qquad \widetilde F(x,J)=(F(x),A(x)\circ J).$$
--   For real $\delta,K,\varepsilon,\ell$, let
--   $$G(\delta,K,\varepsilon,\ell)=
--   \begin{cases}
--   \delta+\varepsilon\ell,&K=0,\\
--   \delta e^{K\ell}+\varepsilon(e^{K\ell}-1)/K,&K\ne0.
--   \end{cases}$$
--   Write $[s,t]_{\mathrm{u}}=[\min(s,t),\max(s,t)]$.
--   Let $S\subset X$ be convex and
--   $A$ be $C$-Lipschitz on $S$, where $C\geq0$. Suppose $\alpha,\beta$
--   solve $x'=F(x)$ and stay in $S$ on $[t_0,t]_{\mathrm u}$. Let an
--   operator curve $J$ satisfy
--   $$J'=A(\alpha)\circ J,\qquad J(t_0)=\operatorname{id}_X.$$
--   Set $h=\beta(t_0)-\alpha(t_0)$ and assume, throughout that interval,
--   $$\|A(\alpha(u))\|\leq K,\qquad
--   \|\beta(u)-\alpha(u)\|\leq L\|h\|.$$
--   Then
--   $$\|\beta(t)-\alpha(t)-J(t)h\|
--   \leq G(0,K,CL^2,|t-t_0|)\|h\|^2.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/VariationRemainder.lean#L35-L80

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Dynamics_Linearization
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

noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

theorem BianchiIX.normalized_variation_remainder {α β : ℝ → NormalizedState}
    {J : ℝ → NormalizedVariation} {t₀ t : ℝ} {S : Set NormalizedState}
    (hS : Convex ℝ S) {K L : ℝ} {C : ℝ≥0}
    (hD : LipschitzOnWith C normalizedDifferential S)
    (hα : ∀ u ∈ uIcc t₀ t, HasDerivAt α (normalizedField (α u)) u)
    (hβ : ∀ u ∈ uIcc t₀ t, HasDerivAt β (normalizedField (β u)) u)
    (hαS : ∀ u ∈ uIcc t₀ t, α u ∈ S) (hβS : ∀ u ∈ uIcc t₀ t, β u ∈ S)
    (hJ : ∀ u ∈ uIcc t₀ t, HasDerivAt J ((normalizedDifferential (α u)).comp (J u)) u)
    (hJinit : J t₀ = ContinuousLinearMap.id ℝ NormalizedState)
    (hDnorm : ∀ u ∈ uIcc t₀ t, ‖normalizedDifferential (α u)‖ ≤ K)
    (hclose : ∀ u ∈ uIcc t₀ t, ‖β u - α u‖ ≤ L * ‖β t₀ - α t₀‖) :
    ‖β t - α t - J t (β t₀ - α t₀)‖ ≤
      gronwallBound 0 K (C * L ^ 2) |t - t₀| * ‖β t₀ - α t₀‖ ^ 2 := by sorry
