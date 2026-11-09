-- Prove2me | Theorems.Thm_AlmostKing_Query_lemma_5
-- name    : AlmostKing.Query.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:51:47.8679+00:00
-- url     : https://prove2.me/theorems/314fa2e4-d72e-4e58-850d-48c0691be5ec
-- title:
--   Lemma 5 — sparse template graphs exist
-- statement:
--   For every $0<\kappa<1$, there is a threshold $N_0$ such that every $n\ge N_0$ admits a $\kappa$-template graph $G$ on $n$ vertices:
--   $$|E(G)|\le n^{4/3},\qquad (1-\kappa)n^{-2/3}|X||Y|\le|E_G(X,Y)|\le(1+\kappa)n^{-2/3}|X||Y|$$
--   for all disjoint vertex sets $X,Y$ of sizes at least $\kappa n$.
--
--   This is the existence statement for the sparse graphs used in the first query stage.
--
--   Differences from the source:
--   - encoding: $[n]=\{1,\ldots,n\}$ → $\mathrm{Fin}\,n=\{0,\ldots,n-1\}$; reason: relabeling by an order-preserving bijection preserves all graph and counting conditions
--   - reading: for sufficiently large $n$ → there exists a natural threshold $N_0$ such that the claim holds for every $n\ge N_0$; reason: this is the stated asymptotic quantifier
-- source:
--   Ziad Ismaili Alaoui, Oded Lachish, Nikhil S. Mande, A King for Almost Everyone, STOC 2027 submission #472 (October 2026), SHA-256 c262b203b2088dcae48025a77e016df4cc78f93c1856a6fac580c7577d8dea92, Lemma 5, p. 6. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/472.pdf

import Mathlib
import Definitions.Def_AlmostKing_Query_Regularity

namespace AlmostKing.Query

/-- Lemma 5, p. 6. -/
theorem lemma_5 : ∀ κ : ℝ, 0 < κ → κ < 1 →
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∃ G : SimpleGraph (Fin n), IsTemplate κ G := by sorry

end AlmostKing.Query
