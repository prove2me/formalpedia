-- Prove2me | Theorems.Thm_CoCoNet_lemma_2
-- name    : CoCoNet.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:50.59975+00:00
-- url     : https://prove2.me/theorems/e893d4d2-5f20-4e00-adaf-c9d457a88649
-- title:
--   Lemma 2 — a self-consistent set of shifted banks exists
-- statement:
--   Let $(m,W)$ be admissible with $I-W$ invertible (Assumption 1), $l\ge0$, $d\in\mathbb R^n_+$, and $H$ the fair-case healthy set. For every $a\in\mathbb R^n$ there is a set of banks $X\subseteq[n]$ with
--   $$H\big(a+(I-W)d_X\big)=X.$$
--
--   The set of banks healthy after shifting by the vectors of $X$ is $X$ itself. This is the fixed point from which Theorem 1 builds an equilibrium of the super-fair case.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - reading: X ⊂ [n] → X : Finset (Fin n), any subset, ∅ and [n] included; reason: the paper writes ⊂ for ⊆ (the proof of Theorem 1 uses X ⊆ [n]); a strict reading is false when every bank is healthy at a + (I − W)d_{[n]}
--   - encoding: fair credit amounts c with lᵢ = cᵢ/mᵢ → credit vector m * l (pointwise); reason: since mᵢ > 0, lᵢ = cᵢ/mᵢ is equivalent to cᵢ = mᵢlᵢ
--   - encoding: H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ} with Φ the fair bijection → Hfair m W l a, built with Function.invFun of the fair map; reason: the fair map is a bijection under the stated hypotheses (Proposition 4), so invFun is its inverse
--   - encoding: d ∈ ℝⁿ₊ fixed throughout §3.3 → d an explicit argument with 0 ≤ d; reason: the statement is asserted for each such d; the proof of Lemma 4 re-instantiates it
--   - encoding: Assumption 1: I − W is invertible → IsUnit (1 - W); reason: the same condition for a square real matrix
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Lemma 2, p.21

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_Hfair
open Matrix

namespace CoCoNet

/-- **Lemma 2 (a self-consistent set of shifted banks).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Lemma 2, p.21: "Under Assumption 1, for all
a ∈ ℝⁿ there is X ⊂ [n] such that H(a + (I − W)d_X) = X."

`H = Hfair` (p.19); `d ∈ ℝⁿ₊`; Assumption 1 (p.18) is `IsUnit (1 - W)`. "X ⊂ [n]" is any subset
(the proof of Theorem 1, p.21, writes X ⊆ [n]).

**Formalization Note.** The fair credit is `m * l`; `0 ≤ l` is a reading (as in Proposition 3). -/
theorem lemma_2 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l d : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hW : IsUnit (1 - W)) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (a : Fin n → ℝ) :
    ∃ X : Finset (Fin n), Hfair m W l (a + (1 - W) *ᵥ restrictTo X d) = X := by sorry

end CoCoNet
