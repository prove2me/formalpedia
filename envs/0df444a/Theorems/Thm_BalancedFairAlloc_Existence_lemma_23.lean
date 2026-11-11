-- Prove2me | Theorems.Thm_BalancedFairAlloc_Existence_lemma_23
-- name    : BalancedFairAlloc.Existence.lemma_23
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:36:54.466293+00:00
-- url     : https://prove2.me/theorems/85bf76f6-361e-4c79-8b94-b279983756db
-- title:
--   Lemma 23 — parametric linear systems with a uniformly strictly feasible point are continuous correspondences
-- statement:
--   Let $B\subseteq\mathbb R^d$ be compact and convex, $a_1,\dots,a_L\in\mathbb R^d$ fixed vectors, $P\subseteq\mathbb R^k$ a parameter set and $b_1,\dots,b_L:P\to\mathbb R$ continuous. Put
--
--   $$K(w)=\{z\in B:\ a_j\cdot z\ge b_j(w)\ \ \forall j\in[L]\}.$$
--
--   Suppose there are $\hat z\in B$ and $\sigma>0$ with $a_j\cdot\hat z\ge b_j(w)+\sigma$ for every $w\in P$ and $j\in[L]$. Then every $K(w)$, $w\in P$, is nonempty, compact and convex, and $w\mapsto K(w)$ has a closed graph on $P$ and is lower hemicontinuous on $P$ (both in the sequential sense of Appendix C).
--
--   The lemma verifies the continuity hypothesis of Lemma 3 for the feasible region of the regularized dual (10).
--
--   Differences from the source:
--   - encoding: ℝ^d, ℝ^k and a_j · z → `Fin d → ℝ`, `Fin k → ℝ`, ∑_l a_j l * z l; b_j given on all of ℝ^k and continuous on P (`ContinuousOn`); reason: only the values on P matter
--   - encoding: closed graph and lower hemicontinuity → `HasClosedGraphOn P K`, `IsLowerHemicontinuousOn P K` (sequential definitions (i), (ii) of Appendix C); reason: these are the paper's definitions
-- source:
--   Cookson, Shah, Verma, Fair and Efficient Balanced Allocations for Additive Valuations, arXiv:2608.06325 (held copy sha256 23649b29…), p. 57 (PDF 59), Lemma 23 (Appendix C)

import Mathlib
import Definitions.Def_BalancedFairAlloc_Existence_Correspondence

namespace BalancedFairAlloc.Existence

theorem lemma_23 (k d L : ℕ) (P : Set (Fin k → ℝ)) (B : Set (Fin d → ℝ))
    (hBc : IsCompact B) (hBv : Convex ℝ B)
    (a : Fin L → Fin d → ℝ) (b : Fin L → (Fin k → ℝ) → ℝ) (hb : ∀ j, ContinuousOn (b j) P)
    (K : (Fin k → ℝ) → Set (Fin d → ℝ))
    (hK : ∀ w, K w = {z | z ∈ B ∧ ∀ j, b j w ≤ ∑ l, a j l * z l})
    (zhat : Fin d → ℝ) (σ : ℝ) (hzB : zhat ∈ B) (hσ : 0 < σ)
    (hmargin : ∀ w ∈ P, ∀ j, b j w + σ ≤ ∑ l, a j l * zhat l) :
    (∀ w ∈ P, (K w).Nonempty ∧ IsCompact (K w) ∧ Convex ℝ (K w)) ∧
    HasClosedGraphOn P K ∧ IsLowerHemicontinuousOn P K := by sorry

end BalancedFairAlloc.Existence
