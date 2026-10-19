-- Prove2me | Theorems.Thm_ContWeatherall_integral_radial
-- name    : ContWeatherall.integral_radial
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:07:06.505487+00:00
-- url     : https://prove2.me/theorems/f6b7b9f1-6b6a-4afe-9ac9-58777d7785bc
-- title:
--   Radial fundamental theorem of calculus
-- statement:
--   For a $C^1$ map $g:E\to G$ into a real Banach space and $x\in E$: $\int_0^1\big((n+1)t^n g(tx)+t^{n+1}Dg(tx)x\big)\,dt=g(x)$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (final integration step)

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Radial fundamental theorem of calculus: `∫₀¹ d/dt (tⁿ⁺¹ g(t x)) dt = g x`, written out. -/
theorem integral_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (n : ℕ) {g : E → G} (hg : ContDiff ℝ 1 g) (x : E) :
    ∫ t in (0 : ℝ)..1, (((n + 1 : ℕ) : ℝ) * t ^ n) • g (t • x) + t ^ (n + 1) • fderiv ℝ g (t • x) x
      = g x := by
  sorry

end ContWeatherall
