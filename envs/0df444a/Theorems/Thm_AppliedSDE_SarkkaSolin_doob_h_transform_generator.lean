-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_doob_h_transform_generator
-- name    : AppliedSDE.SarkkaSolin.doob_h_transform_generator
-- status  : Open
-- author  : @WillR
-- created : 2026-11-13T17:52:15.773817+00:00
-- url     : https://prove2.me/theorems/0569d961-16e4-453b-b917-447a1dd50da6
-- title:
--   General one-dimensional Doob h-transform generator drift identity
-- statement:
--   Särkkä and Solin (2019), Section 7.5, equations (7.73)–(7.79). Let a scalar diffusion have drift b(x) and local variance a(x), and let h(x)>0 be a C² positive conditioning function. For a C² test function φ, the generator of the h-transformed diffusion is h⁻¹A(hφ)−φ h⁻¹Ah. Its drift term equals the original diffusion drift plus a(x)∂x log h(x), while the diffusion coefficient remains a(x). This is a general one-dimensional generator-level identity rather than the earlier Brownian-bridge special case. To obtain the fully conditioned path law of Theorem 7.11 additionally requires the space-time harmonic h, Bayes transition kernel and a valid diffusion martingale problem.
--
--   Representative mathematical statement, subject to the precise formal hypotheses:
--
--   $$
--   A^h\varphi=h^{-1}A(h\varphi)-\varphi h^{-1}Ah
--   $$
-- source:
--   Simo Särkkä and Arno Solin, Applied Stochastic Differential Equations (Cambridge University Press, 2019), Section 7.5, equations (7.73)–(7.79), Theorem 7.11, printed pp. 113–115. https://doi.org/10.1017/9781108186735

import Mathlib
open MeasureTheory
open scoped Topology

theorem AppliedSDE.SarkkaSolin.doob_h_transform_generator
    (b a h φ : ℝ → ℝ)
    (hb : ContDiff ℝ 2 b)
    (ha : ContDiff ℝ 2 a)
    (hh : ContDiff ℝ 2 h)
    (hφ : ContDiff ℝ 2 φ)
    (hpos : ∀ x : ℝ, 0 < h x) :
    ∀ x : ℝ,
      let A : (ℝ → ℝ) → ℝ := fun g =>
        b x * deriv g x +
          a x / 2 * deriv (fun y : ℝ => deriv g y) x
      (A (fun y : ℝ => h y * φ y) - φ x * A h) / h x =
        (b x + a x * (deriv h x / h x)) * deriv φ x +
          a x / 2 * deriv (fun y : ℝ => deriv φ y) x := by
  sorry
