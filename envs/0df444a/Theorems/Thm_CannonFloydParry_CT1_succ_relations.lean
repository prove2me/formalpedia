-- Prove2me | Theorems.Thm_CannonFloydParry_CT1_succ_relations
-- name    : CannonFloydParry.CT1_succ_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-25T19:47:47.413485+00:00
-- url     : https://prove2.me/theorems/68fd65f5-c876-46f4-8bc2-64e0d8c42cb3
-- title:
--   Lemma 5.5 — three relations between the $C_n$ and the $X_k$
-- statement:
--   In $T_1$, for positive integers $k \le n$: i) $C_n = X_n C_{n+1}$; ii) $C_n X_k = X_{k-1} C_{n+1}$; iii) $C_n A = C_{n+1}^2$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 5, p. 237, Lemma 5.5

import Mathlib
import Definitions.Def_CannonFloydParry_T

namespace CannonFloydParry

theorem CT1_succ_relations (k n : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    CT1 n = XT1 n * CT1 (n + 1) ∧
      CT1 n * XT1 k = XT1 (k - 1) * CT1 (n + 1) ∧
      CT1 n * PresentedGroup.of FormalABC.A = CT1 (n + 1) ^ 2 := by
  sorry

end CannonFloydParry
