-- Prove2me | Theorems.Thm_ContWeatherall_alternatizeUncurryFin_apply_cons
-- name    : ContWeatherall.alternatizeUncurryFin_apply_cons
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:04:18.979677+00:00
-- url     : https://prove2.me/theorems/1c36a9ad-81b3-4779-830e-676623af7e20
-- title:
--   Interior product of an alternatization
-- statement:
--   For a continuous linear $L:E\to E[\wedge^{n+1}]\to_LF$ over a nontrivially normed field, $\mathrm{alt}(L)(x,v)=L(x)(v)-\sum_i(-1)^iL(v_i)(x,v_0,\dots,\widehat{v_i},\dots,v_n)$, where `alt` is `alternatizeUncurryFin`.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (the d-of-insertion step)

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Interior product of the alternatization: for `L : E →L E [⋀^Fin (n+1)]→L F`,
`(alt L)(x, v) = L x v - ∑ i, (-1)^i L (v i) (x, v without vᵢ)`. -/
theorem alternatizeUncurryFin_apply_cons {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ}
    (L : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin (n + 1) → E) :
    alternatizeUncurryFin L (Fin.cons x v) =
      L x v - ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • L (v i) (Fin.cons x (i.removeNth v)) := by
  sorry

end ContWeatherall
