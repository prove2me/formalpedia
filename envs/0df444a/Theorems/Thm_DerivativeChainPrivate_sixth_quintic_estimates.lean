-- Prove2me | Theorems.Thm_DerivativeChainPrivate_sixth_quintic_estimates
-- name    : DerivativeChainPrivate.sixth_quintic_estimates
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T05:02:33.425173+00:00
-- url     : https://prove2.me/theorems/398958d2-848c-40ed-921f-f745429bf4b6
-- title:
--   Exact quintic inverse coordinate estimates
-- statement:
--   Assume $\Re\beta,\Im\beta\ge0$, $\Re w>0$, $\Im w\ge0$, $(\Re w)^2\ge5/2$, and $\beta/w=w^2/10-41/140+(459/7840)/(w^2-17/42)$. Put $U=|w|^2$, $D=|w^2-17/42|^2$, $A=(459/7840)(U-17/42)/D$, $B=-(459/7840)(U+17/42)/D$. Then $0\le A\le3/100$, $B\le0$, $(3A-B)/2\le1/15$, and $(\Re w)^2-3(\Im w)^2\ge5/2$. Moreover $\Re\beta/\Re w=((\Re w)^2-3(\Im w)^2)/10-41/140+A$; if $\Im w>0$ then $\Im\beta/\Im w=(3(\Re w)^2-(\Im w)^2)/10-41/140+B$; if $\Im\beta=0$ then $\Im w=0$.
-- source:
--   Local frozen formal commit 5ae66a2275746f86052dbd39f7f4933189ca0395 (not asserted pushed), submission_sync/new_formal/sixth_power/join56/SixthQuinticEstimates.lean, lines 6-66, SHA-256 cc8b6d027cc87bf72e7b3509b62817d6f837aee8266ccb5b3ef2d4e8448fd285.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators

theorem DerivativeChainPrivate.sixth_quintic_estimates (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < w.re) (hy : 0 ≤ w.im) (hX : 5/2 ≤ w.re^2)
    (hinv : β/w = (1/10:ℂ)*w^2-41/140+(459/7840:ℂ)/(w^2-17/42)) :
    let U := w.re^2+w.im^2
    let D := ‖w^2-(17/42:ℂ)‖^2
    let A := (459/7840:ℝ)*(U-17/42)/D
    let B := -(459/7840:ℝ)*(U+17/42)/D
    0 ≤ A ∧ A ≤ 3/100 ∧ B ≤ 0 ∧ (3*A-B)/2 ≤ 1/15 ∧
      5/2 ≤ w.re^2-3*w.im^2 ∧
      β.re/w.re = (1/10:ℝ)*(w.re^2-3*w.im^2)-41/140+A ∧
      (0 < w.im → β.im/w.im = (1/10:ℝ)*(3*w.re^2-w.im^2)-41/140+B) ∧
      (β.im=0 → w.im=0) := by sorry
