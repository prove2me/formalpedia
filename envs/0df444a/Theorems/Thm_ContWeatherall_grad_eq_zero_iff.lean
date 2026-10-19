-- Prove2me | Theorems.Thm_ContWeatherall_grad_eq_zero_iff
-- name    : ContWeatherall.grad_eq_zero_iff
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:26:47.280877+00:00
-- url     : https://prove2.me/theorems/3b357c9b-85e4-4f38-985d-1f14f7945c39
-- title:
--   Spivak §4 (degree 0, outside Thm 4-11): dχ = 0 iff χ is constant
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. For a differentiable $\chi:E\to F$: $d\chi=0$ iff $\chi$ is constant.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (degree-0 case, excluded from Thm 4-11); J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), erratum p. 15 (constant gauge transformations)

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Degree 0: a differentiable function has `dχ = 0` iff it is constant. -/
theorem grad_eq_zero_iff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {χ : E → F} (hχ : Differentiable ℝ χ) :
    grad χ = 0 ↔ ∃ c : F, χ = fun _ => c := by
  sorry

end ContWeatherall
