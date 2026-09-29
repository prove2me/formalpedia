-- Prove2me | solution 1 for minpoly.eq_X_pow_sub_C_of_isCoprime_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/2ff4c448-c8db-5aaf-9dd2-2e8181995300

import Mathlib
import Theorems.Thm_Polynomial_X_pow_sub_C_irreducible_of_isCoprime_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply

set_option autoImplicit false

open Polynomial

theorem solution
    {F L : Type*} [Field F] [Ring L] [Nontrivial L] [Algebra F L]
    (v : F → ℤ) (hv : ∀ x y : F, x ≠ 0 → y ≠ 0 → v (x * y) = v x + v y)
    {n : ℕ} (hn : 0 < n) {u : F} (hu : u ≠ 0) (hcop : IsCoprime (v u) n)
    (θ : L) (hθ : θ ^ n = algebraMap F L u) :
    minpoly F θ = X ^ n - C u := by
  refine (minpoly.eq_of_irreducible_of_monic
    (Polynomial.X_pow_sub_C_irreducible_of_isCoprime_apply v hv hn hu hcop) ?_
    (monic_X_pow_sub_C u hn.ne')).symm
  rw [map_sub, map_pow, aeval_X, aeval_C, hθ, sub_self]

end S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply
end P2MW
export P2MW.S_minpoly_eq_X_pow_sub_C_of_isCoprime_apply (solution)
