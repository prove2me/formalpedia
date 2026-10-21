-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_fourth_selected_sextic_step
-- name    : DerivativeChainPrivate.normalized_fourth_selected_sextic_step
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-20T15:48:08.70398+00:00
-- url     : https://prove2.me/theorems/dc29bc16-d127-4269-8cd0-2bc49b89dd66
-- title:
--   Compatible selected quintic-to-sextic step for a cubic fourth power
-- statement:
--   Fix $\beta\in\mathbb C$ with $\operatorname{Re}\beta\ge0$ and $\operatorname{Im}\beta>0$, in the normalization $q_0(z)=z^3-\frac{11}{2}z-55\beta$. Let $w$ be an actual monic quintic-row root with positive real part, nonnegative imaginary part and $(\operatorname{Re}w)^2\ge5/2$, satisfying the quintic inverse identity
--   $$\frac{\beta}{w}=\frac{w^2}{10}-\frac{23}{80}+\frac{33/640}{w^2-11/24}.$$
--   There exist a finite positive measure $\mu$ concentrated on $[-1/4,3/2]$ and an actual sextic-row root $z$ such that
--   $$\operatorname{Re}w\le\operatorname{Re}z,\quad \operatorname{Im}w\le\operatorname{Im}z,\quad \operatorname{Im}z>0,\quad (\operatorname{Re}z)^2>10/3.$$
--   The sextic equation is
--   $$\frac{275}{14}\beta^2-20\beta z^3+\frac{55}{2}\beta z+z^6-5z^4+\frac{11}{2}z^2-\frac{121}{168}=0.$$
--   The measure represents the fixed shifted branch
--   $$G(u)=i\sqrt{-\left(u^2-\frac{11}{5}u+\frac{121}{120}+\frac{1331}{7560u}\right)}-u+\frac{11}{10}
--   =\int\frac{d\mu(t)}{t-u}\qquad(\operatorname{Im}u>0),$$
--   and the same measure identifies the selected inverse at $z$:
--   $$\frac{\beta}{z}=\frac{28-3\sqrt{70}}{55}z^2-\frac{35-3\sqrt{70}}{50}+\frac{3\sqrt{70}}{55}\int\frac{d\mu(t)}{z^2-t}.$$
--   The incoming point and parameter are retained throughout. This is the selected sixth-row interface used by the subsequent seventh-row construction.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb (revision f5a76eda649f3e995a8ec6b98387b23b64c6debb); complex/SEXTIC_FIXED_COMPLEX_STEP.md, §§1–7, specialized to h=4; complex/H4_SEPTIC_EXTERIOR_BOUNDS.md, §4.

import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_TeschlQM_Herglotz_herglotz_representation
import Theorems.Thm_TeschlQM_Herglotz_stieltjes_inversion_formula
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

theorem DerivativeChainPrivate.normalized_fourth_selected_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-(10/3)*w^3-10*β*w^2+(11/6)*w+(55/12)*β=0)
    (hwinv : β/w = (1/10:ℂ)*w^2-23/80+(33/640:ℂ)/(w^2-11/24)) :
    ∃ μ : Measure ℝ, IsFiniteMeasure μ ∧
      (∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) ∧
      (∀ u : ℂ, 0 < u.im → sexticShift (-11/5) (121/120) (1331/7560) u =
        TeschlQM.Herglotz.borelTransform μ u) ∧
      ∃ z : ℂ,
        (275/14)*β^2-20*β*z^3+(55/2)*β*z+z^6-5*z^4+(11/2)*z^2-121/168=0 ∧
        w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.im ∧ 10/3 < z.re^2 ∧
        β/z = (((28-3*Real.sqrt 70)/55:ℝ):ℂ)*z^2-(((35-3*Real.sqrt 70)/50:ℝ):ℂ)+
          ((3*Real.sqrt 70/55:ℝ):ℂ)*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) := by sorry
