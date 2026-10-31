-- Prove2me | Theorems.Thm_CoCoNet_lemma_4
-- name    : CoCoNet.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:41.331077+00:00
-- url     : https://prove2.me/theorems/899a9b97-6ae0-42be-be36-6b1b69263d6c
-- title:
--   Lemma 4 — some shifted healthy bank stays healthy
-- statement:
--   Let $(m,W)$ be admissible with $I-W$ invertible (Assumption 1), $l\ge0$, $d\in\mathbb R^n_+$, and $H$ the fair-case healthy set. For every $a\in\mathbb R^n$ and every $X\subseteq[n]$,
--   $$\emptyset\ne X\subseteq H(a)\quad\Longrightarrow\quad X\cap H\big(a+(I-W)d_X\big)\ne\emptyset.$$
--
--   Shifting by the vectors of a nonempty set of healthy banks leaves at least one of them healthy.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - encoding: fair credit amounts c with lᵢ = cᵢ/mᵢ → credit vector m * l (pointwise); reason: since mᵢ > 0, lᵢ = cᵢ/mᵢ is equivalent to cᵢ = mᵢlᵢ
--   - encoding: H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ} with Φ the fair bijection → Hfair m W l a, built with Function.invFun of the fair map; reason: the fair map is a bijection under the stated hypotheses (Proposition 4), so invFun is its inverse
--   - encoding: d ∈ ℝⁿ₊ fixed throughout §3.3 → d an explicit argument with 0 ≤ d; reason: the statement is asserted for each such d; the proof of Lemma 4 re-instantiates it
--   - encoding: Assumption 1: I − W is invertible → IsUnit (1 - W); reason: the same condition for a square real matrix
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Lemma 4, p.22

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_Hfair
open Matrix

namespace CoCoNet

/-- **Lemma 4 (some shifted healthy bank stays healthy).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Lemma 4, p.22: "Let a ∈ ℝⁿ be given. Then, under
Assumption 1, for any X ⊆ [n], ∅ ≠ X ⊆ H(a) implies X ∩ H(a + (I − W)d_X) ≠ ∅."

`H = Hfair` (p.19); `d ∈ ℝⁿ₊`; Assumption 1 (p.18) is `IsUnit (1 - W)`.

**Formalization Note.** The fair credit is `m * l`; `0 ≤ l` is a reading (as in Proposition 3). -/
theorem lemma_4 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l d : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hW : IsUnit (1 - W)) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (a : Fin n → ℝ) (X : Finset (Fin n)) (hX : X.Nonempty) (hXH : X ⊆ Hfair m W l a) :
    (X ∩ Hfair m W l (a + (1 - W) *ᵥ restrictTo X d)).Nonempty := by sorry

end CoCoNet
