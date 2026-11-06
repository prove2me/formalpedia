-- Prove2me | Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_extension
-- name    : BianchiIX.normalizedMaxDomain_contains_extension
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T15:42:28.430071+00:00
-- url     : https://prove2.me/theorems/495c6e53-924b-48bd-b7c5-60ed5fbe44d0
-- title:
--   Maximality of the union of exact solution domains
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
--   Let $I_{\max}(x_0,t_0)$ and $\alpha_{\max}$ be the union domain and its
--   compatible solution curve. Let $J\subset\mathbb R$ be open and convex,
--   and let $\beta'=F\circ\beta$ on $J$. If $s\in I_{\max}(x_0,t_0)\cap J$
--   and $\alpha_{\max}(s)=\beta(s)$, then $J\subset I_{\max}(x_0,t_0)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/MaximalFlow.lean#L95-L108

import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
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
open scoped Topology

theorem BianchiIX.normalizedMaxDomain_contains_extension {x₀ : NormalizedState} {t₀ s : ℝ}
    {J : Set ℝ} (hJ : Convex ℝ J) (hoJ : IsOpen J)
    {β : ℝ → NormalizedState}
    (hβ : ∀ t ∈ J, HasDerivAt β (normalizedField (β t)) t)
    (hs : s ∈ normalizedMaxDomain x₀ t₀) (hsJ : s ∈ J)
    (heq : normalizedMaxCurve x₀ t₀ s = β s) : J ⊆ normalizedMaxDomain x₀ t₀ := by sorry
