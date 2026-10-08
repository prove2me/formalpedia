-- Prove2me | Theorems.Thm_BBBV_RandomOracle_theorem_3_1
-- name    : BBBV.RandomOracle.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T16:54:59.633212+00:00
-- url     : https://prove2.me/theorems/614cee88-b4ea-450d-ae97-5c30c9f90813
-- title:
--   Theorem 3.1, p. 7 — unit vectors within Euclidean distance ε give measurement distributions within total variation 4ε
-- statement:
--   Let $\iota$ be a finite set and let $u, v \in \mathbb{C}^{\iota}$ be unit vectors, $\|u\| = \|v\| = 1$, with Euclidean distance $\|u - v\| \le \varepsilon$. Measuring $u$ in the computational basis gives the outcome $c$ with probability $|u_c|^2$, and likewise for $v$. Then the total variation distance between the two outcome distributions satisfies
--   $$\sum_{c \in \iota} \bigl|\, |u_c|^2 - |v_c|^2 \,\bigr| \le 4\varepsilon .$$
--
--   The theorem converts a bound on the distance between two superpositions into a bound on the difference of any observable probability, in particular of acceptance probabilities; it is the step from the hybrid argument (Theorem 3.3) to a statement about what an algorithm outputs.
--
--   **Formalization Note** The total variation distance is the paper's footnote 7, $\sum_x |\mathcal D(x) - \mathcal D'(x)|$, without the factor $1/2$. The constant $4$ is the paper's; it is not sharp.
-- source:
--   Bennett, Bernstein, Brassard and Vazirani, Strengths and weaknesses of quantum computing, arXiv:quant-ph/9701001v1, p. 7, Theorem 3.1 and footnotes 6–7

import Mathlib

namespace BBBV.RandomOracle

theorem theorem_3_1 {ι : Type} [Fintype ι] (u v : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (ε : ℝ) (h : ‖u - v‖ ≤ ε) :
    ∑ c, |‖u c‖ ^ 2 - ‖v c‖ ^ 2| ≤ 4 * ε := by sorry

end BBBV.RandomOracle
