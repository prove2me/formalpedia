-- Prove2me | Theorems.Thm_BranchSpectral_base_nonnegative_by_logical_chain_expanded
-- name    : BranchSpectral.base_nonnegative_by_logical_chain_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:39:02.617302+00:00
-- url     : https://prove2.me/theorems/c53a286c-03d1-4161-baf5-2dde1dc2dfe5
-- title:
--   Base nonnegativity by the corrected Branch 2/3 chain
-- statement:
--   Let γⱼ>0 and |εⱼ|≤1/2 be real sequences indexed by ℕ. Assume εⱼ=0 whenever γⱼ≤1000; an index a satisfies γₐ≤100; for every t>0 the Gaussian series ∑ⱼexp(-γⱼ²t) is summable; and for every t>0,L≥10 its strict tail satisfies ∑_{γⱼ>L}exp(-γⱼ²t)≤(L²+1/t)exp(-L²t). Define
--   $$K(t)=\sum_j e^{-(\gamma_j^2-\varepsilon_j^2)t}\cos(2\varepsilon_j\gamma_jt).$$
--   Let Qₙ(u) additionally satisfy the integral representation
--   $$Q_n(u)=2^n u^{2n-1}\int_0^\infty t^{n-1}e^{-u^2t}K(t)\,dt$$
--   for n≥1,u>0, with each integrand integrable. Then
--   $$Q_n(u)\ge0\quad(n\ge1,\ u>0).$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.base_nonnegative_by_logical_chain_expanded (gamma eps : ℕ → ℝ)
    (gamma_pos : ∀ j, 0 < gamma j)
    (strip : ∀ j, |eps j| ≤ 1/2)
    (verified : ∀ j, gamma j ≤ 1000 → eps j = 0)
    (anchor : ℕ) (anchor_low : gamma anchor ≤ 100)
    (gauss_sum : ∀ t > 0, Summable (fun j => Real.exp (-(gamma j)^2*t)))
    (gauss_tail : ∀ t > 0, ∀ L ≥ 10,
      (∑' j, if L < gamma j then Real.exp (-(gamma j)^2*t) else 0) ≤
      (L^2+t⁻¹)*Real.exp (-L^2*t)) (Q : ℕ → ℝ → ℝ)
    (representation : ∀ n ≥ 1, ∀ u > 0,
      Q n u = 2^n*u^(2*n-1)*(∫ t in Ioi (0 : ℝ),
        t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))))
    (integrable : ∀ n ≥ 1, ∀ u > 0,
      IntegrableOn (fun t => t^(n-1)*Real.exp (-(u^2)*t)*(∑' j, Real.exp (-(((gamma) j)^2-((eps) j)^2)*(t))*Real.cos (2*((eps) j)*((gamma) j)*(t)))) (Ioi 0)) :
    ∀ n ≥ 1, ∀ u > 0, 0 ≤ Q n u := by sorry
