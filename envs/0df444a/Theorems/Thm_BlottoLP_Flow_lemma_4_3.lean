-- Prove2me | Theorems.Thm_BlottoLP_Flow_lemma_4_3
-- name    : BlottoLP.Flow.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:49.594219+00:00
-- url     : https://prove2.me/theorems/67ac2dec-3014-4f26-97ac-19064f2f35e7
-- title:
--   Lemma 4.3, p. 7 — pure strategies correspond one-to-one to canonical paths of the layered graph
-- statement:
--   Fix $K$ battlefields and a player with $N$ troops. For a pure strategy $x=(x_1,\dots,x_K)$ (non-negative integers with $\sum_k x_k=N$) let $s_k=x_1+\dots+x_k$ be the number of troops on the first $k$ battlefields. Then $s_0=0\le s_1\le\dots\le s_K=N$, so $v_{0,s_0}\to v_{1,s_1}\to\dots\to v_{K,s_K}$ is a canonical path of the layered graph. The map
--   $$
--   x\longmapsto (s_0,s_1,\dots,s_K)
--   $$
--   from pure strategies to canonical paths is a bijection.
--
--   This is the bridge from strategies to paths: mixed strategies become distributions over canonical paths, i.e. flows.
--
--   **Formalization Note** The statement is the bijectivity of the specific prefix-sum map `prefixPath`, not merely the existence of some bijection (which would follow from counting alone).
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 7, Lemma 4.3 (and its proof)

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

namespace BlottoLP.Flow

/-- Lemma 4.3: the prefix-sum map is a one-to-one correspondence between the pure strategies of a
player with `N` troops on `K` battlefields and the canonical paths of his layered graph. -/
theorem lemma_4_3 (K N : ℕ) :
    Function.Bijective (prefixPath : Pure K N → CanonicalPath K N) := by sorry

end BlottoLP.Flow
