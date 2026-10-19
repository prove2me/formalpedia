-- Prove2me | Theorems.Thm_ContWeatherall_alternating_sum_cons_removeNth
-- name    : ContWeatherall.alternating_sum_cons_removeNth
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-14T22:00:46.904988+00:00
-- url     : https://prove2.me/theorems/0f3fcd2d-f0bb-4657-bd3f-bde5e9f0d271
-- title:
--   Alternating sum of front-moves is (n+1)·f
-- statement:
--   For an alternating map $f$ of $n+1$ arguments over a commutative ring and any $v$, $\sum_{i=0}^n(-1)^i f(v_i,v_0,\dots,\widehat{v_i},\dots,v_n)=(n+1)f(v)$.
-- source:
--   M. Spivak, Calculus on Manifolds (W. A. Benjamin, 1965), Theorem 4-11 (Poincaré lemma) and its proof (sign bookkeeping in the computation of d(Iω))

import Mathlib
import Definitions.Def_ContWeatherall_defs

open CategoryTheory ContinuousAlternatingMap
open scoped ContDiff

namespace ContWeatherall

/-- Moving the `i`-th vector of `v` to the front with sign `(-1)^i` and summing over `i`
multiplies an alternating map of `n + 1` arguments by `n + 1`. -/
theorem alternating_sum_cons_removeNth {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (f : M [⋀^Fin (n + 1)]→ₗ[R] N) (v : Fin (n + 1) → M) :
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (i : ℕ) • f (Fin.cons (v i) (i.removeNth v)) = (n + 1) • f v := by
  sorry

end ContWeatherall
