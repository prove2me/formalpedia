-- Prove2me | Theorems.Thm_ContWeatherall_poincare
-- name    : ContWeatherall.poincare
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:17:48.946856+00:00
-- url     : https://prove2.me/theorems/5943a1b1-8d68-4cb3-91a0-b4615245acae
-- title:
--   Spivak Thm 4-11: Poincaré lemma (closed ⇒ exact)
-- statement:
--   Throughout, $E$ is a real normed space, $F$ a real normed space (Banach where stated), forms are Mathlib's `E → E [⋀^Fin k]→L[ℝ] F`, $d$ is `extDeriv` ($d\omega(x)(v_0,\dots,v_k)=\sum_i(-1)^iD\omega(x)(v_i)(v_0,\dots,\widehat{v_i},\dots,v_k)$), smooth means `ContDiff ℝ ∞`, and $(K\omega)(x)(v)=\int_0^1t^k\,\omega(tx)(x,v)\,dt$ for a $(k+1)$-form $\omega$. If $F$ is complete and $\omega$ is a smooth form of degree $k+1\ge1$ with $d\omega=0$, there is a smooth $k$-form $\eta$ with $d\eta=\omega$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Poincaré lemma: a smooth closed form of degree `k + 1 ≥ 1` on a real normed space `E`, with
values in a real Banach space `F`, is exact with a smooth primitive. -/
theorem poincare {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ} {w : E → E [⋀^Fin (k + 1)]→L[ℝ] F}
    (hw : ContDiff ℝ ∞ w) (hclosed : extDeriv w = 0) :
    ∃ η : E → E [⋀^Fin k]→L[ℝ] F, ContDiff ℝ ∞ η ∧ extDeriv η = w := by
  sorry

end ContWeatherall
