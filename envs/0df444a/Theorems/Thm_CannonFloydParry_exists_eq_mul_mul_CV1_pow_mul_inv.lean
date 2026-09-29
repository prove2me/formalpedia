-- Prove2me | Theorems.Thm_CannonFloydParry_exists_eq_mul_mul_CV1_pow_mul_inv
-- name    : CannonFloydParry.exists_eq_mul_mul_CV1_pow_mul_inv
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:24:08.869979+00:00
-- url     : https://prove2.me/theorems/ef16ec7c-1161-447b-a2d0-21745e25d880
-- title:
--   p. 248 — every element of $V_1$ is $p\pi C_n^mq^{-1}$
-- statement:
--   Every $g \in V_1$ can be written $g = p\,\pi\,C_n^m\,q^{-1}$ with $p$, $q$ positive elements of $V_1$, natural numbers $m < n + 2$, and $\pi \in \Pi(n)$.
--
--   **Formalization Note.** This is the $V_1$ counterpart of Theorem 5.7; the source derives it in one sentence inside the proof of Theorem 6.9. $C_0 = 1$ and $\Pi(0)$ is trivial, so $n = 0$ gives $g = pq^{-1}$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 248, proof of Theorem 6.9

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem exists_eq_mul_mul_CV1_pow_mul_inv (g : V1) :
    ∃ (p q π : V1) (m n : ℕ), IsPositiveV1 p ∧ IsPositiveV1 q ∧ m < n + 2 ∧ π ∈ PiSub n ∧
      g = p * π * CV1 n ^ m * q⁻¹ := by
  sorry

end CannonFloydParry
