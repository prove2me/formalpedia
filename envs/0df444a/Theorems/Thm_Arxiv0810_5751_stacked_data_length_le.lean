-- Prove2me | Theorems.Thm_Arxiv0810_5751_stacked_data_length_le
-- name    : Arxiv0810_5751.stacked_data_length_le
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:40:50.408948+00:00
-- url     : https://prove2.me/theorems/df6b245b-13f4-4f3c-b207-808338766fe4
-- title:
--   Section II: the stacked data vector has length $M\le 2N(N-1)$
-- statement:
--   Let the array have $N$ stations. Let $B$ be any set of cross-correlation baselines $(p,q)$, $1\le p<q\le N$, and let $\mathbf y$ stack the four entries of $\mathrm{vec}(\mathbf V_{pq})$ for each $(p,q)\in B$. Then the length $M$ of $\mathbf y$ satisfies
--
--   $$M\le 2N(N-1),$$
--
--   with equality when all $N(N-1)/2$ cross correlations are used.
--
--   This count bounds the number of complex constraints available to estimate $\boldsymbol\theta$.
--
--   **Formalization Note** $M$ is the cardinality of the index set of $\mathbf y$. The paper's further remarks, that $P$ is "typically" proportional to $KN$ and that there are then enough constraints "for large enough $N$ and small enough $K$", are heuristic and are not part of the statement.
-- source:
--   Yatawatta, Zaroubi, de Bruyn, Koopmans and Noordam, Radio interferometric calibration using the SAGE algorithm, arXiv:0810.5751v1 (2008), claim c014; Section II (Data Model), text after eq. (4), PDF p. 2

import Mathlib
import Definitions.Def_Arxiv0810_5751_Basic

open MeasureTheory Matrix
open scoped ComplexOrder

namespace Arxiv0810_5751

theorem stacked_data_length_le (N : ℕ) :
    (∀ B : Finset (Fin N × Fin N), B ⊆ crossBaselines N →
      Fintype.card (VisIndex B) ≤ 2 * N * (N - 1)) ∧
    Fintype.card (VisIndex (crossBaselines N)) = 2 * N * (N - 1) := by sorry

end Arxiv0810_5751
