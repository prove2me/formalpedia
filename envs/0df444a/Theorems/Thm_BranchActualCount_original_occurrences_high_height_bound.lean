-- Prove2me | Theorems.Thm_BranchActualCount_original_occurrences_high_height_bound
-- name    : BranchActualCount.original_occurrences_high_height_bound
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-17T12:24:29.659802+00:00
-- url     : https://prove2.me/theorems/f0480ee7-50e9-4856-8765-830322b29327
-- title:
--   Closed high-height bound for the original xi zero occurrences
-- statement:
--   Let xi(s)=(1+s(s-1) completedRiemannZeta₀(s))/2. Index its upper-half-plane zeros by their locations and analytic multiplicities. For every real T≥1000 and every finite collection F of these occurrences whose imaginary parts are at most T, |F|≤T sqrt(T). The boundary at T is included. This is a high-height bound and makes no claim about the corresponding unit constant below 1000 or about global RH.
-- source:
--   Underlying analytic zero count: smmercuri/zeta commit 3dab6480a82f1bfc5de0a59550e279cf50490033; PrimeNumberTheoremAnd commit 0a2c672d7533437e50f7a72596cb0ecd17352fbe. Apache-2.0 attribution retained. Original-xi occurrence bridge and composition by Desenvolvimento RH, coordinated by Ricardo Marangoni Brandão Bueno.

import Mathlib

theorem BranchActualCount.original_occurrences_high_height_bound :
    let f : ℂ → ℂ := fun s => (1+s*(s-1)*completedRiemannZeta₀ s)/2
    let I := (z : {s : ℂ // f s=0 ∧ 0<s.im}) × Fin (analyticOrderNatAt f z.val)
    ∀ T ≥ (1000 : ℝ), ∀ F : Finset I,
      (∀ i ∈ F, i.1.val.im ≤ T) → (F.card : ℝ) ≤ T*Real.sqrt T := by sorry
