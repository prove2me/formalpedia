-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fifth_selected_sextic_step
-- name    : DerivativeChainPrivate.normalized_fifth_selected_sextic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T18:50:43.977015+00:00
-- url     : https://prove2.me/theorems/44c00c47-7b69-4163-8797-f8698b51b130
-- title:
--   Compatible selected quintic-to-sextic step for a cubic fifth power
-- statement:
--   Use the normalization $q(z)=z^3-7z-91\beta$, where $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$. Suppose $w$ is a root of the displayed monic quintic derivative row, $\operatorname{Re}w>0$, $\operatorname{Im}w\ge0$, $(\operatorname{Re}w)^2\ge5/2$, and
--   $$\frac\beta w=\frac{w^2}{10}-\frac{16}{55}+\frac{441/7865}{w^2-14/33}.$$
--   There exist a finite positive measure $\mu$ concentrated on $[-1/4,3/2]$ and a sextic-row root $z$ with
--   $$\operatorname{Re}w\le\operatorname{Re}z,\quad\operatorname{Im}w\le\operatorname{Im}z,\quad\operatorname{Im}z>0,\quad(\operatorname{Re}z)^2>7/2.$$
--   The measure represents the shifted branch associated with $H(u)=u^2-35u/17+490/561+686/(5049u)$, as specified in the formal statement, and
--   $$\frac\beta z=\frac{110-3\sqrt{1122}}{182}z^2-\frac{680-15\sqrt{1122}}{884}+\frac{3\sqrt{1122}}{182}\int\frac{d\mu(t)}{z^2-t}.$$
--   The root $z$ satisfies the exact sextic equation in the statement; the incoming root and parameter are retained.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb/f5a76eda649f3e995a8ec6b98387b23b64c6debb#file-fifth-md; complex/SEXTIC_FIXED_COMPLEX_STEP.md, h=5 specialization; lower/H5_LOWER_MIDDLE_COMPLETION.md.

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_TeschlQM_Herglotz_herglotz_representation
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_fifth_selected_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(70/39)*w+(140/33)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-16/55+(441/7865:ℂ)/(w^2-14/33)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 < u.im → sexticShift (-35/17) (490/561) (686/5049) u =
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : ℂ,
        (182/11)*β^2-20*β*z^3+(280/11)*β*z+z^6-5*z^4+(70/13)*z^2-98/143=0 ∧
        w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.im ∧ 7/2 < z.re^2 ∧
        β/z = (((110-3*Real.sqrt 1122)/182:ℝ):ℂ)*z^2-(((680-15*Real.sqrt 1122)/884:ℝ):ℂ)+
          ((3*Real.sqrt 1122/182:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by sorry
