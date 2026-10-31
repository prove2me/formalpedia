-- Prove2me | Theorems.Thm_CoCoNet_corollary_1
-- name    : CoCoNet.corollary_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:06.105954+00:00
-- url     : https://prove2.me/theorems/7f0116d8-5bcf-4fe6-a3a3-b670f668e4e7
-- title:
--   Corollary 1 — the cyclical monotonicity of $h$
-- statement:
--   Let $(m,W)$ be admissible with $I-W$ invertible (Assumption 1), $l\ge0$, $d\in\mathbb R^n_+$, $\hat a\in\mathbb R^n$, and $h(X)=H(\hat a+(I-W)d_X)$. For every $X\subseteq[n]$:
--   1. if $X\subseteq Y\subseteq h(X)$ then $h(Y)\subseteq h(X)$;
--   2. if $h(X)\subseteq Y\subseteq X$ then $h(X)\subseteq h(Y)$;
--   3. if $X\subseteq h^2(X)\subsetneq h(X)$ then $h^2(X)\subseteq h^3(X)\subsetneq h(X)$;
--   4. if $h(X)\subsetneq h^2(X)\subseteq X$ then $h(X)\subsetneq h^3(X)\subseteq h^2(X)$.
--
--   These facts force the iterates $h^k(H(\hat a))$ to be squeezed between their predecessors and to become constant after finitely many steps, which gives the fixed point of Lemma 2.
--
--   **Formalization Note** The four items are one conjunction; $h^k$ is `Nat.iterate`.
--
--   Differences from the source:
--   - reading: no sign condition on the thresholds l stated → 0 ≤ l; reason: the paper asserts that the sets S_{B,C,H} partition ℝⁿ (p.12), which holds iff l ≥ 0; in the paper's setting lᵢ ≥ cᵢ/mᵢ with nonnegative debts cᵢ; without it the sets read off s overlap and Φ is not continuous
--   - encoding: fair credit amounts c with lᵢ = cᵢ/mᵢ → credit vector m * l (pointwise); reason: since mᵢ > 0, lᵢ = cᵢ/mᵢ is equivalent to cᵢ = mᵢlᵢ
--   - encoding: H(a) = {i : Φ⁻¹(a)ᵢ > ℓᵢ} with Φ the fair bijection → Hfair m W l a, built with Function.invFun of the fair map; reason: the fair map is a bijection under the stated hypotheses (Proposition 4), so invFun is its inverse
--   - encoding: d ∈ ℝⁿ₊ fixed throughout §3.3 → d an explicit argument with 0 ≤ d; reason: the statement is asserted for each such d; the proof of Lemma 4 re-instantiates it
--   - encoding: Assumption 1: I − W is invertible → IsUnit (1 - W); reason: the same condition for a square real matrix
--   - encoding: banks [n] = {1, …, n}; vectors in ℝⁿ; matrix W = (w_ij) → banks Fin n (0-based); vectors Fin n → ℝ; W : Matrix (Fin n) (Fin n) ℝ with W i j = w_ij; reason: same objects, relabelled from 0
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, Corollary 1, p.22

import Mathlib
import Definitions.Def_CoCoNet_IsAdmissible
import Definitions.Def_CoCoNet_hmap

namespace CoCoNet

/-- **Corollary 1 (monotonicity behaviour of `h`).**
Balter, Schweizer & Vera, arXiv:2011.06474v1, Corollary 1, p.22: "Under Assumption 1, let
X ⊆ [n].
(i) If X ⊆ Y ⊆ h(X) then h(Y) ⊆ h(X).
(ii) If h(X) ⊆ Y ⊆ X then h(X) ⊆ h(Y).
(iii) If X ⊆ h²(X) ⊊ h(X) then h²(X) ⊆ h³(X) ⊊ h(X).
(iv) If h(X) ⊊ h²(X) ⊆ X then h(X) ⊊ h³(X) ⊆ h²(X)."

Here `h = hmap m W l d ahat`, `h(X) = H(â + (I − W)d_X)` (p.22), with `â` and `d ∈ ℝⁿ₊` fixed;
`hᵏ` is `h^[k]`; `⊊` is `⊂`.

**Formalization Note.** The four items are one conjunction. The fair credit is `m * l`; `0 ≤ l`
is a reading (as in Proposition 3). -/
theorem corollary_1 {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l d ahat : Fin n → ℝ)
    (hadm : IsAdmissible m W) (hW : IsUnit (1 - W)) (hl : 0 ≤ l) (hd : 0 ≤ d)
    (X : Finset (Fin n)) :
    (∀ Y : Finset (Fin n), X ⊆ Y → Y ⊆ hmap m W l d ahat X →
        hmap m W l d ahat Y ⊆ hmap m W l d ahat X) ∧
    (∀ Y : Finset (Fin n), hmap m W l d ahat X ⊆ Y → Y ⊆ X →
        hmap m W l d ahat X ⊆ hmap m W l d ahat Y) ∧
    (X ⊆ (hmap m W l d ahat)^[2] X → (hmap m W l d ahat)^[2] X ⊂ hmap m W l d ahat X →
        (hmap m W l d ahat)^[2] X ⊆ (hmap m W l d ahat)^[3] X ∧
          (hmap m W l d ahat)^[3] X ⊂ hmap m W l d ahat X) ∧
    (hmap m W l d ahat X ⊂ (hmap m W l d ahat)^[2] X → (hmap m W l d ahat)^[2] X ⊆ X →
        hmap m W l d ahat X ⊂ (hmap m W l d ahat)^[3] X ∧
          (hmap m W l d ahat)^[3] X ⊆ (hmap m W l d ahat)^[2] X) := by sorry

end CoCoNet
