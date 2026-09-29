-- Prove2me | Theorems.Thm_CannonFloydParry_exists_eq_mul_CT1_pow_mul_inv
-- name    : CannonFloydParry.exists_eq_mul_CT1_pow_mul_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:48:33.848444+00:00
-- url     : https://prove2.me/theorems/0b897c92-ac61-4abb-8681-a8eb0decafda
-- title:
--   Theorem 5.7 — every element of $T_1$ is $pC_n^mq^{-1}$
-- statement:
--   Every $g \in T_1$ can be written $g = p\,C_n^m\,q^{-1}$ with $p$, $q$ positive elements of $T_1$ (products of nonnegative powers of the $X_i$) and $m$, $n$ natural numbers with $m < n + 2$.
--
--   **Formalization Note.** $C_0 = 1$, so $n = 0$ or $m = 0$ gives $g = pq^{-1}$, as the source allows.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 239, Theorem 5.7

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem exists_eq_mul_CT1_pow_mul_inv (g : T1) :
    ∃ (p q : T1) (m n : ℕ), IsPositiveT1 p ∧ IsPositiveT1 q ∧ m < n + 2 ∧
      g = p * CT1 n ^ m * q⁻¹ := by
  sorry

end CannonFloydParry
