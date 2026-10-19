-- Prove2me | Theorems.Thm_ContWeatherall_h1Vanishes
-- name    : ContWeatherall.h1Vanishes
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:27:10.586836+00:00
-- url     : https://prove2.me/theorems/5ed1ecc2-1c03-4b17-ad09-37d4e9d6d9a1
-- title:
--   Spivak Thm 4-11, degree 1: H¹ = 0, closed 1-forms are gradients
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete, every smooth closed 1-form is $d\chi$ for a smooth $\chi:E\to F$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (degree 1); J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4 fn. 9 (topology set aside on Minkowski space)

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- `H¹ = 0`: every smooth closed 1-form is `dχ` of a smooth function. -/
theorem h1Vanishes (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] : H1Vanishes E F := by
  sorry

end ContWeatherall
