-- Prove2me | Theorems.Thm_CannonFloydParry_piV1_relations
-- name    : CannonFloydParry.piV1_relations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-26T10:25:17.142316+00:00
-- url     : https://prove2.me/theorems/431d5a9d-ac18-4532-9031-2c41da01e5b9
-- title:
--   Lemma 6.3 — the $\pi_i$ satisfy the Coxeter relations of the symmetric group
-- statement:
--   In $V_1$, for every $i \ge 0$: i) $\pi_i^2 = 1$; ii) $(\pi_{i+1}\pi_i)^3 = 1$; iii) $\pi_i\pi_j = \pi_j\pi_i$ whenever $j \ge i + 2$.
-- source:
--   Cannon, J. W., Floyd, W. J., Parry, W. R., Introductory notes on Richard Thompson's groups, L'Enseignement Mathématique (2) 42 (1996) 215–256, https://doi.org/10.5169/seals-87877, section 6, p. 244, Lemma 6.3

import Mathlib
import Definitions.Def_CannonFloydParry_V

namespace CannonFloydParry

theorem piV1_relations (i : ℕ) :
    piV1 i ^ 2 = 1 ∧ (piV1 (i + 1) * piV1 i) ^ 3 = 1 ∧
      ∀ j, i + 2 ≤ j → piV1 i * piV1 j = piV1 j * piV1 i := by
  sorry

end CannonFloydParry
