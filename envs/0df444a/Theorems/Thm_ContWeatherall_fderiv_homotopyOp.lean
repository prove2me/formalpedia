-- Prove2me | Theorems.Thm_ContWeatherall_fderiv_homotopyOp
-- name    : ContWeatherall.fderiv_homotopyOp
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:14:18.487904+00:00
-- url     : https://prove2.me/theorems/d7c33bc0-c65c-4b6f-9586-25ce2221e7c1
-- title:
--   Derivative of K under the integral sign
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete and $\omega$ is smooth, then $D(K\omega)(x)h=\int_0^1t^k\big(t\,(D\omega(tx)h)(x,\cdot)+\omega(tx)(h,\cdot)\big)\,dt$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (differentiation under the integral sign)

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Differentiation under the integral sign for the radial homotopy operator. -/
theorem fderiv_homotopyOp {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) (x h : E) :
    fderiv ℝ (homotopyOp w) x h = ∫ t in (0 : ℝ)..1,
      t ^ k • (t • (fderiv ℝ w (t • x) h).curryLeft x + (w (t • x)).curryLeft h) := by
  sorry

end ContWeatherall
