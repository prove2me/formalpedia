-- Prove2me | Theorems.Thm_BranchSpectral_spectral_kernel_pos
-- name    : BranchSpectral.spectral_kernel_pos
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:05:33.887296+00:00
-- url     : https://prove2.me/theorems/50a24bcc-bdb2-4646-a203-ae2aa95344af
-- title:
--   Conditional strict positivity of the spectral kernel
-- statement:
--   Let γⱼ>0 and |εⱼ|≤1/2 be real sequences indexed by ℕ. Assume εⱼ=0 whenever γⱼ≤1000; an index a satisfies γₐ≤100; for every t>0 the Gaussian series ∑ⱼexp(-γⱼ²t) is summable; and for every t>0,L≥10 its strict tail satisfies ∑_{γⱼ>L}exp(-γⱼ²t)≤(L²+1/t)exp(-L²t). Define
--   $$K(t)=\sum_j e^{-(\gamma_j^2-\varepsilon_j^2)t}\cos(2\varepsilon_j\gamma_jt).$$
--   For every t>0, K(t)>0.
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.spectral_kernel_pos (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) :
    ∀ t > 0, 0 < (∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t))) := by sorry
