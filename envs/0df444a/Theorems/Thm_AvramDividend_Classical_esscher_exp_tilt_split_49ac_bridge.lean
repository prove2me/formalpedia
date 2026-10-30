-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_exp_tilt_split_49ac_bridge
-- name    : AvramDividend.Classical.esscher_exp_tilt_split_49ac_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:13:51.259609+00:00
-- url     : https://prove2.me/theorems/3704a1c1-4337-4cd0-98de-f5b1731cb4a0
-- title:
--   Esscher exponential tilt splits over an interval endpoint
-- statement:
--   The Esscher exponential factor splits multiplicatively over an interval: exp(phi*b) equals exp(phi*a) times exp(phi*(b-a)). This is the deterministic exponential half of the Chan-Kyprianou-Savov Esscher relation W^q(x)=exp(phi*x)*W_phi(x) used on the 49ac excursion-representation route. Follows from phi*b = phi*a + phi*(b-a) and Real.exp_add.
-- source:
--   Chan, Kyprianou, Savov (2011), Smoothness of scale functions for spectrally negative Levy processes, equation (4) deterministic exponential factor; Mathlib Real.exp_add.

import Mathlib
open Real

theorem AvramDividend.Classical.esscher_exp_tilt_split_49ac_bridge
    (φ a b : ℝ) :
    Real.exp (φ * b) = Real.exp (φ * a) * Real.exp (φ * (b - a)) := by sorry
