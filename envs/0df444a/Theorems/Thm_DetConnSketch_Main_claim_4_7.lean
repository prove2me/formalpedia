-- Prove2me | Theorems.Thm_DetConnSketch_Main_claim_4_7
-- name    : DetConnSketch.Main.claim_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:11.052175+00:00
-- url     : https://prove2.me/theorems/48bf4133-62e9-4ec9-9ebb-dc5ed745c306
-- title:
--   Claim 4.7 — for uniform $A,B$ over $\mathbb F_q$ ($q\ge16$), $\Pr[A^\top NB=0]\le q^{-\ell\min(\ell,R)/2}$ where $R=\operatorname{rank}N\ge1$
-- statement:
--   Let $N$ be an $s\times s$ matrix with entries in $\{-1,0,1\}$, with at most $k$ nonzero entries above the diagonal and at most $10\sqrt k$ nonzero entries in every row and every column. Let $\mathbb F_q$ be a finite field with $q \ge 16$ elements and let $R \ge 1$ be the rank of $N$ over $\mathbb F_q$. If $A, B \in \mathbb F_q^{s\times \ell}$ are independent and uniformly random, then
--   $$\Pr\big[A^\top N B = 0\big] \le q^{-\ell\cdot\min(\ell, R)/2}.$$
--
--   In the proof of Lemma 4.4 this bounds the chance that a random sketch matrix fails to detect one fixed nonzero low-degree remainder $N = M'_{\bar U,\bar U}$.
--
--   Differences from the source:
--   - encoding: M′_{Ū,Ū} ∈ {−1,0,1}^{(n−u)×(n−u)} → any N : Matrix (Fin s) (Fin s) ℤ with entries in {−1, 0, 1}, cast entrywise into F; reason: s = n − u is an arbitrary size; the claim's hypotheses are on the matrix only
--   - encoding: F_q with q ≥ 16 → any finite field F with Fintype.card F ≥ 16; rank R of N.map Int.cast; reason: F_q is the field with q elements
--   - encoding: Pr over independent uniform A, B ∈ F_q^{(n−u)×ℓ} → number of pairs (A, B) with Aᵀ N B = 0 divided by q^{2sℓ}; reason: the uniform product measure is counting
--   - encoding: parameter k (real in the application) → k : ℕ; reason: for real k ≥ 0, use ⌈k⌉: the sparsity upper bounds only increase, while the conclusion is independent of k
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 26 (PDF 30), Claim 4.7

import Mathlib
import Definitions.Def_DetConnSketch_Main_SketchMatrices

namespace DetConnSketch.Main

/-- Claim 4.7: let `N` be a square `{−1, 0, 1}`-valued matrix with at most `k` nonzero entries
above the diagonal and at most `10√k` nonzero entries in every row and column, and let
`R ≥ 1` be its rank over a finite field `F` with `q = |F| ≥ 16`. For independent uniform
`A, B ∈ F^{s×ℓ}`, `Pr[Aᵀ N B = 0] ≤ q^{−ℓ·min(ℓ,R)/2}`. The probability is the number of pairs
`(A, B)` with `Aᵀ N B = 0` divided by `q^{2sℓ}`. -/
theorem claim_4_7 (F : Type) [Field F] [Fintype F] (hq : 16 ≤ Fintype.card F)
    (s ℓ k R : ℕ) (N : Matrix (Fin s) (Fin s) ℤ)
    (hN : ∀ i j, N i j = -1 ∨ N i j = 0 ∨ N i j = 1)
    (habove : nnzAboveDiag N ≤ k)
    (hrow : ∀ i, (rowNnz N i : ℝ) ≤ 10 * Real.sqrt k)
    (hcol : ∀ j, (colNnz N j : ℝ) ≤ 10 * Real.sqrt k)
    (hrank : (N.map (Int.cast : ℤ → F)).rank = R) (hR : 1 ≤ R) :
    (Nat.card {AB : Matrix (Fin s) (Fin ℓ) F × Matrix (Fin s) (Fin ℓ) F //
        AB.1.transpose * N.map (Int.cast : ℤ → F) * AB.2 = 0} : ℝ) /
        (Fintype.card F : ℝ) ^ (2 * s * ℓ) ≤
      (Fintype.card F : ℝ) ^ (-((ℓ * min ℓ R : ℕ) : ℝ) / 2) := by sorry

end DetConnSketch.Main
