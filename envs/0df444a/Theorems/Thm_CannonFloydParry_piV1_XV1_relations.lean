-- Prove2me | Theorems.Thm_CannonFloydParry_piV1_XV1_relations
-- name    : CannonFloydParry.piV1_XV1_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:24:53.028371+00:00
-- url     : https://prove2.me/theorems/bcacd702-6969-4141-8956-a75abea990b2
-- title:
--   Lemma 6.2 — $\pi_i$ past $X_j$, and $C_i$ past $\pi_j$
-- statement:
--   In $V_1$, for a positive integer $i$: i) if $0 \le j < i$ then $\pi_iX_j = X_j\pi_{i+1}$; ii) if $j \ge i + 2$ then $\pi_iX_j = X_j\pi_i$; iii) if $i > j > 0$ then $C_i\pi_j = \pi_{j-1}C_i$.
--
--   **Formalization Note.** The source's $j$ is an integer; every case forces $j \ge 0$, so $j$ is a natural number here.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 243, Lemma 6.2

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem piV1_XV1_relations (i : ℕ) (hi : 0 < i) :
    (∀ j, j < i → piV1 i * XV1 j = XV1 j * piV1 (i + 1)) ∧
      (∀ j, i + 2 ≤ j → piV1 i * XV1 j = XV1 j * piV1 i) ∧
      (∀ j, 0 < j → j < i → CV1 i * piV1 j = piV1 (j - 1) * CV1 i) := by
  sorry

end CannonFloydParry
