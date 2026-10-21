-- Prove2me | Theorems.Thm_DynDoubleAuction_TwoSided_lemma_5_2_range
-- name    : DynDoubleAuction.TwoSided.lemma_5_2_range
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:42.318551+00:00
-- url     : https://prove2.me/theorems/3afaac6f-324e-4d9c-b054-1a8427355e9d
-- title:
--   Lemma 5.2 — promises remain coupled and within range
-- statement:
--   Let every agent begin with the same promise $w^1\in[0,\bar w^1]$, where $\bar w^t=(T-t+1)\mu$. Along every value path in $[0,\bar v]^{n+1}$, at each period $t\le T+1$ every agent's promise remains coupled and satisfies
--
--   $$0\le w_i^t\le\bar w^t,\qquad w_i^t=w_0^t.$$
--
--   In particular, all terminal promises are zero. This is the state-range part of Lemma 5.2 and supplies the feasibility invariant for the recursive mechanism.
--
--   **Formalization Note** The pathwise support condition makes explicit the paper's bounded-support convention; the probability measure's support condition is also in the standing assumptions.
-- source:
--   Balseiro, Mirrokni, Paes Leme & Zuo, Dynamic Double Auctions: Towards First Best, SSRN 3213460 (version of November 15, 2018), p. 25, Lemma 5.2

import Mathlib
import Definitions.Def_DynDoubleAuction_TwoSided_Model

namespace DynDoubleAuction.TwoSided

open MeasureTheory Filter Topology

/-- Lemma 5.2: at every state, all agents have one promise in the permitted range. -/
theorem lemma_5_2_range {n : ℕ} (M : Market n) (hM : Standing M)
    (T : ℕ) (w1 : ℝ) (hw1 : 0 ≤ w1 ∧ w1 ≤ wbar M T 1)
    (vs : ℕ → Fin (n + 1) → ℝ)
    (hvs : ∀ k j, vs k j ∈ Set.Icc 0 M.vbar) :
    ∀ k ≤ T, ∀ j : Fin (n + 1),
      0 ≤ state M T w1 vs k j ∧
      state M T w1 vs k j ≤ wbar M T (k + 1) ∧
      state M T w1 vs k j = state M T w1 vs k 0 := by sorry
end DynDoubleAuction.TwoSided
