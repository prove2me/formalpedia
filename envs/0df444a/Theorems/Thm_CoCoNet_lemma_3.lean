-- Prove2me | Theorems.Thm_CoCoNet_lemma_3
-- name    : CoCoNet.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:57.982385+00:00
-- url     : https://prove2.me/theorems/8c469bf1-a9e6-4fc8-8d86-a4c75960e343
-- title:
--   Lemma 3 — $H(a+(I-W)d_X)\subseteq H(a)\cup X$
-- statement:
--   Let $(m,W)$ be admissible, $l\ge0$, $d\in\mathbb R^n_+$, and let $H$ be the fair-case healthy set. For every $a\in\mathbb R^n$ and every $X\subseteq[n]$,
--   $$H\big(a+(I-W)d_X\big)\subseteq H(a)\cup X.$$
--
--   Shifting the asset vector by the vectors of the banks in $X$ can make healthy only banks that were healthy already or that belong to $X$.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - generalization: §3.3 assumes I − W invertible 'throughout this section' (p.18) → no IsUnit (1 - W) hypothesis; reason: unlike Lemma 4, Lemma 3 does not name Assumption 1, and its proof (p.34) uses only Proposition 4 and the sign pattern of L⁻¹_{B,C}(I − W), neither of which needs I − W invertible; the instances with I − W invertible are the section's claim
--   - encoding: fair credit amounts c with lᵢ = cᵢ/mᵢ → credit vector m * l (pointwise); reason: since mᵢ > 0, lᵢ = cᵢ/mᵢ is equivalent to cᵢ = mᵢlᵢ
--   - encoding: H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ} with Φ the fair bijection → Hfair m W l a, built with Function.invFun of the fair map; reason: the fair map is a bijection under the stated hypotheses (Proposition 4), so invFun is its inverse
--   - encoding: d ∈ ℝⁿ₊ fixed throughout §3.3 → d an explicit argument with 0 ≤ d; reason: the statement is asserted for each such d; the proof of Lemma 4 re-instantiates it
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Lemma 3, p.22

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_Hfair
open Matrix

namespace CoCoNet

/-- **Lemma 3 (shifting by `X` makes healthy only banks of `H(a) ∪ X`).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Lemma 3, p.22: "Let a ∈ ℝⁿ be given. For any
X ⊆ [n], H(a + (I − W)d_X) ⊆ H(a) ∪ X."

`H = Hfair` is the healthy set in the fair case (p.19) and `d ∈ ℝⁿ₊` is any vector of credit
reductions (p.19).

**Formalization Note.** Stated without Assumption 1 (a generalization: §3.3 imposes it "throughout
this section", p.18, but Lemma 3 does not name it and its proof, p.34, only uses Lemma 5's sign
pattern of `L⁻¹_{B,C}(I − W)` and Proposition 4). The fair credit is `m * l`; `0 ≤ l` is a reading
(as in Proposition 3). -/
theorem lemma_3 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l d : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hl : 0 ≤ l) (hd : 0 ≤ d) (a : Fin n → ℝ) (X : Finset (Fin n)) :
    Hfair m W l (a + (1 - W) *ᵥ restrictTo X d) ⊆ Hfair m W l a ∪ X := by sorry

end CoCoNet
