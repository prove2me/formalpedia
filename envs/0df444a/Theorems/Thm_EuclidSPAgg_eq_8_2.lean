-- Prove2me | Theorems.Thm_EuclidSPAgg_eq_8_2
-- name    : EuclidSPAgg.eq_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:45.352536+00:00
-- url     : https://prove2.me/theorems/136b8db9-5c27-4b5c-87aa-5f4bd9d280b2
-- title:
--   Display (8.2) [Gravin–Jia] — $R_{n,d}\le\rho=\sqrt{6\sqrt3-8}<2$
-- statement:
--   For every population size $n\ge2$ and every dimension $d\ge1$, the coordinate-wise median satisfies
--   $$
--   R_{n,d}\le\rho:=\sqrt{6\sqrt3-8}<2 .
--   $$
--   This is the upper bound of Gravin and Jia (STOC 2025, Theorem 1, spatial exponent 2), quoted by the paper and not proved there. In the proof of Theorem 8.5 it guarantees that a competitor beating the median has ratio below $n-1$.
--
--   **Formalization Note** Both clauses are stated: the bound on $R_{n,d}$ and the numerical inequality $\rho<2$.
--
--   Differences from the source:
--   - reading: for every population size → for every n ≥ 2; reason: the paper defines AR, hence R_{n,d}, for n ≥ 2
-- source:
--   Jia, Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality, arXiv:2609.19394 (held version, sha256 891e6125…), display (8.2), p.34 (PDF p.36), quoting Gravin–Jia, STOC 2025, doi:10.1145/3717823.3718156, Theorem 1

import Mathlib
import Definitions.Def_EuclidSPAgg_medianRatio
open RBMSensitivity (E)

namespace EuclidSPAgg

/-- **Display (8.2)** (Jia, *Strategyproof Aggregation in Euclidean Spaces: Rigidity and Median Optimality*, arXiv:2609.19394 (held version, sha256 891e6125…), p.34 (PDF p.36)), quoting Gravin–Jia [GJ25, Theorem 1, spatial
exponent 2] (STOC 2025, doi:10.1145/3717823.3718156): the coordinate-wise median satisfies, for
every population size and every finite dimension, `R_{n,d} ≤ ρ := √(6√3 − 8) < 2`.

**Formalization Note** This is an external result: the paper cites it and does not prove it.
"Every population size" is every `n ≥ 2`, the range on which the paper defines `AR`. Both clauses
of the display are stated: the bound and `ρ < 2`. -/
theorem eq_8_2 (n d : ℕ) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    medianRatio n d ≤ ENNReal.ofReal (Real.sqrt (6 * Real.sqrt 3 - 8)) ∧
      Real.sqrt (6 * Real.sqrt 3 - 8) < 2 := by sorry

end EuclidSPAgg
