-- Prove2me | Theorems.Thm_ComplementFreeCA_CFRounding_sum_layers_ge
-- name    : ComplementFreeCA.CFRounding.sum_layers_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T00:15:41.582773+00:00
-- url     : https://prove2.me/theorems/8a42c04a-cc10-40bb-a16f-1af1e51f87f8
-- title:
--   Step (iii), per bidder: complement freeness gives Σ_r v_i(S_i^r) ≥ v_i(S_i)
-- statement:
--   Let $v$ be a normalized, complement-free valuation, let $\sigma=(S_1,\dots,S_n)$ be a preallocation in which every item appears in at most $k$ bundles, and let $S_i^r$ be the layers of step (ii). Then for every bidder $i$,
--   $$v(S_i)\le\sum_{r=1}^{k} v(S_i^r).$$
--
--   This is where complement freeness enters the proof of Theorem 3.1: since $S_i=\bigcup_r S_i^r$, subadditivity bounds the value of the whole bundle by the sum of the values of its layers.
--
--   **Formalization Note** Normalization $v(\emptyset)=0$ is used because some layers may be empty (and for $k=0$, where $S_i=\emptyset$).
-- source:
--   Dobzinski, Nisan, Schapira, Approximation Algorithms for Combinatorial Auctions with Complement-Free Bidders, Math. Oper. Res. 35(1), 2010, p. 6, §3.1, proof of Theorem 3.1, step (iii), first sentence

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction
import Definitions.Def_ComplementFreeCA_CFRounding_Algorithm

namespace ComplementFreeCA.CFRounding

theorem sum_layers_ge {n m : ℕ} (v : Finset (Fin m) → ℝ) (hnorm : IsNormalized v)
    (hsub : IsSubadditive v) (σ : Fin n → Finset (Fin m)) (k : ℕ)
    (hcount : ∀ j, count σ j ≤ k) (i : Fin n) :
    v (σ i) ≤ ∑ r ∈ Finset.Icc 1 k, v (layer σ i r) := by sorry

end ComplementFreeCA.CFRounding
