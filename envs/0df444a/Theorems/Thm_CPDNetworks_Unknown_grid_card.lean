-- Prove2me | Theorems.Thm_CPDNetworks_Unknown_grid_card
-- name    : CPDNetworks.Unknown.grid_card
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:54.215526+00:00
-- url     : https://prove2.me/theorems/195e5197-784a-468d-84d0-4238284cf1b1
-- title:
--   p. 12, after (13) — the dyadic grid 𝒯 lies in 𝒟_T = {1, …, T − 1} and has |𝒯| ≤ 2 log₂ T points
-- statement:
--   Let $T\ge2$ and let $\mathcal T=\mathcal T^L\cup\mathcal T^R$ be the dyadic grid (13),
--   $$\mathcal T^L=\{2^k:k=0,\dots,\lfloor\log_2(T/2)\rfloor\},\qquad\mathcal T^R=\{T-2^k:k=0,\dots,\lfloor\log_2(T/2)\rfloor\}.$$
--   Then every grid point is a possible change point, $\mathcal T\subseteq\mathcal D_T=\{1,\dots,T-1\}$, and
--   $$|\mathcal T|\le2\log_2 T.$$
--
--   The cardinality bound is what the union bound over the grid costs in the threshold (15), through the factor $\log_2T$ inside the logarithm.
--
--   **Formalization Note.** The paper writes $|\mathcal T|=2+2\lfloor\log_2(T/2)\rfloor\le2\log_2(T)$. The equality fails when $\mathcal T^L$ and $\mathcal T^R$ overlap (for $T=4$, $\mathcal T=\{1,2,3\}$), so only the inequality, which is what the proof of Lemma 5 uses, is stated.
-- source:
--   Enikeeva and Klopp, Change-point detection in dynamic networks with missing links, arXiv:2106.14470v2, p. 12, display (13) and the sentence after it

import Mathlib
import Definitions.Def_HighDimProb_RandomMatrices_matrixOpNorm
import Definitions.Def_CPDNetworks_Unknown_Setting

open scoped Matrix
open HighDimProb.RandomMatrices

namespace CPDNetworks.Unknown

/-- p. 12, after (13): the dyadic grid lies in `𝒟_T` and has at most `2 log₂ T` points. -/
theorem grid_card (T : ℕ) (hT : 2 ≤ T) :
    ((dyadicGrid T).card : ℝ) ≤ 2 * Real.logb 2 T ∧ dyadicGrid T ⊆ DT T := by sorry

end CPDNetworks.Unknown
