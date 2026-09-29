-- Prove2me | Theorems.Thm_Farey_one_one_mem_pairs
-- name    : Farey.one_one_mem_pairs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-10T10:47:56.5088+00:00
-- url     : https://prove2.me/theorems/aaaa16b0-05b8-4368-92ac-5bc2b03c71ee
-- title:
--   The Farey dissection of positive order is nonempty
-- statement:
--   For every $P \ge 1$ the pair $(1,1)$ — representing the fraction $1/1$ — lies in the Farey dissection of order $P$.
--
--   $$P \ge 1 \;\Longrightarrow\; (1,1) \in \mathcal{F}_P.$$
--
--   In particular the dissection is nonempty, which is what lets one split a sum over the arcs by isolating a distinguished term. In the circle method the arc at $1/1$ is the one carrying the main term of the asymptotic.
-- source:
--   Standard Farey-dissection facts. See R. C. Vaughan, The Hardy-Littlewood Method, 2nd ed., Cambridge University Press 1997, Chapter 2; Hardy & Wright, An Introduction to the Theory of Numbers, Chapter III.

import Definitions.Def_Farey
import Mathlib

namespace Farey

theorem one_one_mem_pairs {P : ℕ} (hP : 0 < P) : ((1 : ℕ), (1 : ℕ)) ∈ pairs P := by
  sorry

end Farey
