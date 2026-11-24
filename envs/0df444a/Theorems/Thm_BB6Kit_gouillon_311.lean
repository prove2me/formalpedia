-- Prove2me | Theorems.Thm_BB6Kit_gouillon_311
-- name    : BB6Kit.gouillon_311
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-24T08:10:36.28204+00:00
-- url     : https://prove2.me/theorems/2d767790-ee8d-4a32-9cbb-0681f3718f64
-- title:
--   Gouillon's zero estimate (kit Prop. 3.11), real form: no nonzero $P$ of degree $(K,L)$ vanishes on $\Sigma_1+\Sigma_2+\Sigma_3$
-- statement:
--   Gouillon's zero estimate in the form of Proposition 3.11 of the Mignotte–Voutier kit, specialised to real point sets and real coefficients (the source works over $\mathbb C$; real data is a special case, since every complex direction $(\lambda,\mu)$ has a nonzero real or imaginary part).
--
--   **Theorem.** Let $K,L\ge1$. Let $\Sigma_1,\Sigma_2,\Sigma_3\subset\mathbb R^2\times\mathbb R^{\times}$ be finite sets, with the group law $(x_1,x_2,y)+(x_1',x_2',y')=(x_1+x_1',x_2+x_2',yy')$. Assume:
--
--   - (3.17) $\#\{\lambda x_1+\mu x_2\}_{\Sigma_1}>K$ for all $(\lambda,\mu)\ne(0,0)$, and $\#\{y\}_{\Sigma_1}>L$;
--   - (3.18) $\#\{(\lambda x_1+\mu x_2,y)\}_{\Sigma_2}>2KL$ for all $(\lambda,\mu)\ne(0,0)$, and $\#\{(x_1,x_2)\}_{\Sigma_2}>K^2$;
--   - (3.19) $\#\Sigma_3>3K^2L$.
--
--   Let $P=\sum_{(a,b,e)\in D}c_{a,b,e}X_1^aX_2^bY^e$, where $D$ is a finite set of exponent triples with $a+b\le K$ and $e\le L$. If $P$ vanishes on $\Sigma_1+\Sigma_2+\Sigma_3$, then every $c_{a,b,e}$ is $0$.
--
--   This is the deep input of the kit's zero lemma: Lemma 3.12, a special case of Théorème 2.1 of Gouillon's thesis. It contains no BB(6)-specific parameters.
-- source:
--   Mignotte & Voutier (appendix by Laurent), A kit for linear forms in three logarithms, Math. Comp. (2023), arXiv:2205.08899, Proposition 3.11 and Lemma 3.12 (Gouillon, thesis, Théorème 2.1 with m = 2).

import Mathlib

namespace BB6Kit
theorem gouillon_311 (K L : ℕ) (hK : 0 < K) (hL : 0 < L) (S1 S2 S3 : Finset (ℝ × ℝ × ℝ))
    (hy : ∀ p ∈ S1 ∪ S2 ∪ S3, p.2.2 ≠ 0)
    (h317a : ∀ l m : ℝ, (l, m) ≠ (0, 0) → K < (S1.image (fun p => l * p.1 + m * p.2.1)).card)
    (h317b : L < (S1.image (fun p => p.2.2)).card)
    (h318a : ∀ l m : ℝ, (l, m) ≠ (0, 0) → 2 * K * L < (S2.image (fun p => (l * p.1 + m * p.2.1, p.2.2))).card)
    (h318b : K ^ 2 < (S2.image (fun p => (p.1, p.2.1))).card)
    (h319 : 3 * K ^ 2 * L < S3.card)
    (D : Finset (ℕ × ℕ × ℕ)) (hD : ∀ q ∈ D, q.1 + q.2.1 ≤ K ∧ q.2.2 ≤ L) (c : ℕ × ℕ × ℕ → ℝ)
    (hvan : ∀ p1 ∈ S1, ∀ p2 ∈ S2, ∀ p3 ∈ S3,
      ∑ q ∈ D, c q * (p1.1 + p2.1 + p3.1) ^ q.1 * (p1.2.1 + p2.2.1 + p3.2.1) ^ q.2.1 *
        (p1.2.2 * p2.2.2 * p3.2.2) ^ q.2.2 = 0) :
    ∀ q ∈ D, c q = 0 := by
  sorry
end BB6Kit
