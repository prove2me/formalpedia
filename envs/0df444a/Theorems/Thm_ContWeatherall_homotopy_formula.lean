-- Prove2me | Theorems.Thm_ContWeatherall_homotopy_formula
-- name    : ContWeatherall.homotopy_formula
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:14:40.812711+00:00
-- url     : https://prove2.me/theorems/c0d5bcea-6ccb-4f9d-9102-4b9bdf7e9911
-- title:
--   Spivak Thm 4-11 (proof): homotopy formula dK + Kd = id
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete and $\omega$ is a smooth form of degree $k+1\ge1$, then $d(K\omega)+K(d\omega)=\omega$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (the identity ω = d(Iω) + I(dω))

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- The homotopy formula `d K + K d = id` on smooth forms of degree `k + 1 ≥ 1`. -/
theorem homotopy_formula {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) : extDeriv (homotopyOp w) + homotopyOp (extDeriv w) = w := by
  sorry

end ContWeatherall
