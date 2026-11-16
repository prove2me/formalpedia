-- Prove2me | Theorems.Thm_BranchSpectral_kernel_summable
-- name    : BranchSpectral.kernel_summable
-- status  : Open
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:46:44.873383+00:00
-- url     : https://prove2.me/theorems/fcb90a2d-daa7-4f72-8285-d09e7cb39f50
-- title:
--   Summability of the signed spectral kernel
-- statement:
--   Let g,e be real sequences with |eⱼ|≤1/2, and fix t>0. If ∑ⱼ exp(-gⱼ²t) is summable, then ∑ⱼ exp(-(gⱼ²-eⱼ²)t)cos(2eⱼgⱼt) is summable.
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.kernel_summable (g e : ℕ → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => (fun (g t : ℝ) => Real.exp (-g^2*t)) (g j) t)) :
    Summable (fun j => (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) (g j) (e j) t) := by sorry
