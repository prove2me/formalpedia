-- Prove2me | Theorems.Thm_CannonFloydParry_XT1_mul_XT1
-- name    : CannonFloydParry.XT1_mul_XT1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:47:22.48415+00:00
-- url     : https://prove2.me/theorems/c424726d-1ca8-4050-bdec-6ef4824cea4c
-- title:
--   p. 236 — $X_n X_k = X_k X_{n+1}$ in $T_1$ for $k < n$
-- statement:
--   In $T_1$, for natural numbers $k < n$, $X_n X_k = X_k X_{n+1}$, where $X_0 = A$ and $X_m = A^{-(m-1)}BA^{m-1}$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 236, after Lemma 5.4

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem XT1_mul_XT1 (k n : ℕ) (hkn : k < n) : XT1 n * XT1 k = XT1 k * XT1 (n + 1) := by
  sorry

end CannonFloydParry
