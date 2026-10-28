-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_convex_shift_tendsto_atTop
-- name    : AvramDividend.Classical.esscher_convex_shift_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:41:48.369297+00:00
-- url     : https://prove2.me/theorems/ddb9146a-7085-4793-8240-267bfd66017e
-- title:
--   Convex exponent with positive root grows to infinity after Esscher shift
-- statement:
--   If a real-valued function ψ is convex on [0,∞), has ψ(0)=0, and satisfies ψ(φ)=q with φ,q>0, then g(β)=ψ(φ+β)−q tends to +∞ as β tends to +∞. The proof derives the exact linear secant lower bound qβ ≤ φg(β) for β≥0. This is an analytic theorem requiring no process law or Wiener–Hopf factorisation.
-- source:
--   Mathlib.Analysis.Convex.Slope ConvexOn.secant_mono_aux1; Kuznetsov–Kyprianou–Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes, §2, convexity of ψ.

import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic.Linarith

open Set Filter

theorem AvramDividend.Classical.esscher_convex_shift_tendsto_atTop
    (psi : ℝ → ℝ) (phi q : ℝ)
    (hconv : ConvexOn ℝ (Ici (0 : ℝ)) psi)
    (hpsi0 : psi 0 = 0) (hphi : 0 < phi)
    (hq : 0 < q) (hpsiphi : psi phi = q) :
    Tendsto (fun beta : ℝ => psi (phi + beta) - q) atTop atTop := by sorry
