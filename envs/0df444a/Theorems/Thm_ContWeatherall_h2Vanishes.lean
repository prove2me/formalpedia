-- Prove2me | Theorems.Thm_ContWeatherall_h2Vanishes
-- name    : ContWeatherall.h2Vanishes
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-18T19:30:03.111317+00:00
-- url     : https://prove2.me/theorems/b5060aaf-5a8a-41da-b668-7e6e93b80cb6
-- title:
--   Spivak Thm 4-11, degree 2: H² = 0, closed 2-forms are field strengths
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete, for any predicate $P$, every smooth closed 2-form $B$ with $P(B)$ is $dA$ for a smooth 1-form $A$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (degree 2); J. O. Weatherall, Understanding Gauge, Philos. Sci. 83 (2016) 1039-1049, https://arxiv.org/abs/1505.02229 (page numbers refer to arXiv v2), §4 (every Maxwell field derives from a potential on Minkowski space)

import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- `H² = 0`: every smooth closed 2-form (satisfying `P`) is `dA` of a smooth 1-form. -/
theorem h2Vanishes {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (P : (E → E [⋀^Fin 2]→L[ℝ] F) → Prop) : H2Vanishes P := by
  sorry

end ContWeatherall
