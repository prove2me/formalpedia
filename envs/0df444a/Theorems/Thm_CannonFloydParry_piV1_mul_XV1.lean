-- Prove2me | Theorems.Thm_CannonFloydParry_piV1_mul_XV1
-- name    : CannonFloydParry.piV1_mul_XV1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:25:38.603216+00:00
-- url     : https://prove2.me/theorems/a752ad92-3f95-47e9-b15d-5683c0c65eb0
-- title:
--   Lemma 6.4 — moving $\pi_i$ past $X_j$
-- statement:
--   In $V_1$, for all $i, j \ge 0$: i) $\pi_iX_j = X_j\pi_i$ if $j \ge i + 2$; ii) $\pi_iX_{i+1} = X_i\pi_{i+1}\pi_i$; iii) $\pi_iX_i = X_{i+1}\pi_i\pi_{i+1}$; iv) $\pi_iX_j = X_j\pi_{i+1}$ if $j < i$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 245, Lemma 6.4

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem piV1_mul_XV1 (i j : ℕ) :
    (i + 2 ≤ j → piV1 i * XV1 j = XV1 j * piV1 i) ∧
      piV1 i * XV1 (i + 1) = XV1 i * piV1 (i + 1) * piV1 i ∧
      piV1 i * XV1 i = XV1 (i + 1) * piV1 i * piV1 (i + 1) ∧
      (j < i → piV1 i * XV1 j = XV1 j * piV1 (i + 1)) := by
  sorry

end CannonFloydParry
