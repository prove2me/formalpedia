-- Prove2me | Theorems.Thm_BianchiIX_contDiff_normalizedField
-- name    : BianchiIX.contDiff_normalizedField
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-04T13:54:17.291914+00:00
-- url     : https://prove2.me/theorems/4769521f-ec60-424f-9109-fc51d3367318
-- title:
--   Analytic regularity of the normalized Bianchi IX vector field
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
--   The vector field $F:X\to X$ is $C^n$ for every order
--   $n\in\mathbb N\cup\{\infty,\omega\}$, where $C^\omega$ denotes analytic
--   regularity. In particular, the normalized equation has a smooth vector field
--   throughout the state space.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/Normalized.lean#L29-L34

import Definitions.Def_BianchiIX_Dynamics_Normalized
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

noncomputable section
open BianchiIX
open Set

theorem BianchiIX.contDiff_normalizedField (n : WithTop ℕ∞) : ContDiff ℝ n normalizedField := by sorry
