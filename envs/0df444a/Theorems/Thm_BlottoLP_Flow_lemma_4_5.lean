-- Prove2me | Theorems.Thm_BlottoLP_Flow_lemma_4_5
-- name    : BlottoLP.Flow.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:51.927837+00:00
-- url     : https://prove2.me/theorems/59b8ff91-e796-473a-9cca-6fde2b400025
-- title:
--   Lemma 4.5, p. 8 — every unit flow is the flow of a mixed strategy with at most |E| pure strategies in its support
-- statement:
--   Let $K\ge 1$ and let $F$ be a flow of size $1$ from $v_{0,0}$ to $v_{K,N}$ in the layered graph of a player with $N$ troops (the constraints (a) of Linear Program 1). Then there is a mixed strategy $\sigma$ of that player whose flow is exactly $F$,
--   $$
--   F_\sigma = F,
--   $$
--   and whose support has at most as many pure strategies as the layered graph has edges:
--   $$
--   |\{x : \sigma(x)\neq 0\}|\ \le\ |E|,\qquad |E| = K\,\frac{(N+1)(N+2)}{2}.
--   $$
--
--   Together with Corollary 4.4 this shows that the unit flows are exactly the flows of mixed strategies, so Linear Program 1 may optimize over flows instead of over the exponentially many pure strategies.
--
--   **Formalization Note** The paper's "polynomial size support" is pinned to the bound its proof gives ("the total number of these paths will not exceed the total number of edges in the graph"). The hypothesis $K\ge 1$ is added: with $K=0$ and $N>0$ there are no pure strategies, while every edge function on the empty edge set is vacuously a unit flow.
-- source:
--   Behnezhad, Dehghani, Derakhshan, Hajiaghayi, Seddighin, Faster and Simpler Algorithm for Optimal Strategies of Blotto Game, arXiv preprint (arXiv:1612.04029, PDF of 2016-12-28), p. 8, Lemma 4.5 (support bound from its proof)

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model

open Finset

namespace BlottoLP.Flow

/-- Lemma 4.5: every flow of size `1` from `v_{0,0}` to `v_{K,N}` is the flow of a mixed strategy
whose support has at most as many pure strategies as the layered graph has edges. -/
theorem lemma_4_5 (K N : ℕ) (hK : 1 ≤ K) (F : Edge K N → ℝ) (hF : IsUnitFlow F) :
    ∃ σ : Pure K N → ℝ, IsMixed σ ∧ flowOf σ = F ∧
      (univ.filter (fun x : Pure K N => σ x ≠ 0)).card ≤ Fintype.card (Edge K N) := by sorry

end BlottoLP.Flow
