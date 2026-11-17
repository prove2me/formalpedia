-- Prove2me | Theorems.Thm_BranchSpectral_spectral_head_tail_expanded
-- name    : BranchSpectral.spectral_head_tail_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:03:15.906072+00:00
-- url     : https://prove2.me/theorems/c31eefe1-4efb-4654-8b71-d2e0d373cbbd
-- title:
--   Spectral head-tail bound
-- statement:
--   Let γⱼ>0 and |εⱼ|≤1/2 be real sequences indexed by ℕ. Assume εⱼ=0 whenever γⱼ≤1000; an index a satisfies γₐ≤100; for every t>0 the Gaussian series ∑ⱼexp(-γⱼ²t) is summable; and for every t>0,L≥10 its strict tail satisfies ∑_{γⱼ>L}exp(-γⱼ²t)≤(L²+1/t)exp(-L²t). Define
--   $$K(t)=\sum_j e^{-(\gamma_j^2-\varepsilon_j^2)t}\cos(2\varepsilon_j\gamma_jt).$$
--   If t>0,L≥10, γₐ≤L and all atoms with γⱼ≤L are nonnegative, then
--   $$K(t)\ge e^{-10000t}-e^{t/4}(L^2+t^{-1})e^{-L^2t}.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.spectral_head_tail_expanded (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (t L : ℝ) (ht : 0 < t)
    (hL : 10 ≤ L) (ha : gamma anchor ≤ L)
    (hnear : ∀ j, gamma j ≤ L → 0 ≤ (Real.exp (-(((gamma j))^2-((eps j))^2)*(t))*Real.cos (2*((eps j))*((gamma j))*(t)))) :
    Real.exp (-10000*t) - Real.exp (t/4)*(L^2+t⁻¹)*Real.exp (-L^2*t) ≤
      (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by sorry
