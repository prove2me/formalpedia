-- Prove2me | Theorems.Thm_BianchiIX_corrected_divergence_amplitude_pos
-- name    : BianchiIX.corrected_divergence_amplitude_pos
-- status  : Proved
-- author  : @trppppp
-- created : 2026-11-05T05:49:30.902845+00:00
-- url     : https://prove2.me/theorems/2d5d4ebb-78fd-4641-9129-4bb1a5159151
-- title:
--   Corrected divergence is positive throughout the positive-wall region
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
--   Define $H(a,b,c)=(abc)^{2/3}$ and
--   $$\Delta(q,h)=\frac{2(q+4h)}{1+4h}.$$
--   Real powers and division have their total Lean meanings.
--   If $a,b,c>0$, then
--   $$\Delta(K(a,b,c),H(a,b,c))>0.$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flux.lean#L139-L145

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section

theorem BianchiIX.corrected_divergence_amplitude_pos
    {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < correctedDivergence (curvature a b c) (wallAmplitude a b c) := by sorry
