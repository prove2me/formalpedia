-- Prove2me | Theorems.Thm_BFFPyramidal_muMeasure_divisorClosure_image_mul
-- name    : BFFPyramidal.muMeasure_divisorClosure_image_mul
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-13T18:27:34.872764+00:00
-- url     : https://prove2.me/theorems/22299dfc-5ad0-4532-8878-e929379e1615
-- title:
--   Scaling law for the totient measure of a divisor closure
-- statement:
--   For every positive integer $k$ and every finite set $R$ of positive integers,
--   $$ \mu\!\left(D(kR)\right) \;=\; k \, \mu\!\left(D(R)\right), $$
--   where $kR = \{km : m \in R\}$, $D$ is the divisor closure and $\mu$ is the totient measure $\mu(S) = \sum_{m \in S}\varphi(m)$.
--
--   This scaling law is the arithmetic engine of the induction in Berger-Felzenbaum-Fraenkel: it converts a multiplicative change in a set of subgroup orders into a multiplicative change in the measure bounding the size of a union of cosets. For $R = \{m\}$ it reduces to Gauss's identity $\sum_{d \mid m}\varphi(d) = m$.
--
--   **Formalization note.** $kR$ is `R.image (fun m => k * m)`. Both hypotheses matter: $k > 0$, and every member of $R$ is positive (otherwise `Nat.divisors 0 = ∅` makes the two sides disagree).
-- source:
--   Berger--Felzenbaum--Fraenkel 1987, Remark on the multiplicity of a partition of a group into cosets, Fund. Math. 128 (1987) 139-144, https://doi.org/10.4064/fm-128-3-139-144, p. 141, eq. (14)

import Mathlib
import Definitions.Def_BFFPyramidal_arithmetic

namespace BFFPyramidal

theorem muMeasure_divisorClosure_image_mul (k : ℕ) (hk : 0 < k) (R : Finset ℕ)
    (hR : ∀ m ∈ R, 0 < m) :
    muMeasure (divisorClosure (R.image (fun m => k * m)))
      = k * muMeasure (divisorClosure R) := by
  sorry

end BFFPyramidal
