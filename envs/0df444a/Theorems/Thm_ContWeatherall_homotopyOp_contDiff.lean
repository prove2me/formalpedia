-- Prove2me | Theorems.Thm_ContWeatherall_homotopyOp_contDiff
-- name    : ContWeatherall.homotopyOp_contDiff
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-14T22:10:52.145147+00:00
-- url     : https://prove2.me/theorems/825b0eb7-df4e-4b1d-aa65-98d61808e029
-- title:
--   Spivak Thm 4-11 (proof): K preserves smoothness
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete and $\omega$ is a smooth $(k+1)$-form, then $K\omega$ is a smooth $k$-form.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (I ω is a C^∞ form)

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- The radial homotopy operator maps smooth forms to smooth forms. -/
theorem homotopyOp_contDiff {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (homotopyOp w) := by
  sorry

end ContWeatherall
