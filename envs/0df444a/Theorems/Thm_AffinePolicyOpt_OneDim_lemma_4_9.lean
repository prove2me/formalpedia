-- Prove2me | Theorems.Thm_AffinePolicyOpt_OneDim_lemma_4_9
-- name    : AffinePolicyOpt.OneDim.lemma_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T13:08:18.878841+00:00
-- url     : https://prove2.me/theorems/3c26a91a-d7d5-440b-83a9-0dabbcc18551
-- title:
--   Lemma 4.9, p. 24 — the affine cost dominates the convex cost: h(b₀ + Σ b_i w_i) ≤ z₀ + Σ z_i w_i on [0,1]^{k+1}
-- statement:
--   Under the hypotheses of Lemma 4.8 (generators $b_j>0$ with strictly decreasing ratios $a_j/b_j$, a convex $h$, matched indices $0=s(1)<\dots<s(n)=k+1$, and coefficients $z_0,\dots,z_{k+1}$, $K_{s(2)},\dots,K_{s(n)}$ satisfying (51)–(53)), the affine cost $z(w)=z_0+\sum_{i=1}^{k+1}z_iw_i$ dominates the convex cost on the whole hypercube:
--   $$h\Big(b_0+\sum_{i=1}^{k+1}b_iw_i\Big)\le z_0+\sum_{i=1}^{k+1}z_iw_i\qquad\text{for all }w\in\mathcal H_{k+1}=[0,1]^{k+1}.$$
--
--   This is the robust domination condition (13) in the induction step of Theorem 3.1.
--
--   **Formalization Note** As in Lemma 4.8, "the affine cost computed by Algorithm 2" is replaced by the system (51)–(53) as hypotheses, cross-multiplied, with the two misprints of (53) corrected and $b_j>0$ added. Indices are stored 0-based.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, p. 24, Lemma 4.9, with (51)–(53), p. 22

import Mathlib
import Definitions.Def_AffinePolicyOpt_OneDim_Zonogon

namespace AffinePolicyOpt.OneDim

/-- Lemma 4.9: under the hypotheses of Lemma 4.8, the affine cost dominates the convex cost on
the whole hypercube: `h(b_0 + Σ_i b_i w_i) ≤ z_0 + Σ_i z_i w_i` for all `w ∈ [0, 1]^{k+1}`. -/
theorem lemma_4_9 (k : ℕ) (b0 : ℝ) (a b : Fin (k + 1) → ℝ) (hb : ∀ g, 0 < b g)
    (hab : GenOrdered a b) (h : ℝ → ℝ) (hh : ConvexOn ℝ Set.univ h)
    (z0 : ℝ) (z : Fin (k + 1) → ℝ)
    (n : ℕ) (s : Fin (n + 1) → ℕ) (hs : StrictMono s) (hs0 : s 0 = 0)
    (hsn : s (Fin.last n) = k + 1) (K : Fin n → ℝ)
    -- (51), matching
    (h51m : ∀ i, z0 + psum z 0 (s i) = h (b0 + psum b 0 (s i)))
    -- (51), alignment, cross-multiplied
    (h51a : ∀ i : Fin n, ∀ g : Fin (k + 1), s i.castSucc ≤ (g : ℕ) → (g : ℕ) < s i.succ →
      z g + a g = K i * b g)
    -- (52)
    (h52 : Antitone K)
    -- (53), cross-multiplied
    (h53 : ∀ i : Fin n, ∀ j : ℕ, s i.castSucc < j → j < s i.succ →
      h (b0 + psum b 0 j) - h (b0 + psum b 0 (s i.castSucc)) + psum a (s i.castSucc) j ≤
          K i * psum b (s i.castSucc) j ∧
        K i * psum b j (s i.succ) ≤
          h (b0 + psum b 0 (s i.succ)) - h (b0 + psum b 0 j) + psum a j (s i.succ)) :
    ∀ w ∈ cube (k + 1), h (b0 + ∑ i, b i * w i) ≤ z0 + ∑ i, z i * w i := by sorry

end AffinePolicyOpt.OneDim
