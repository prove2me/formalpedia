-- Prove2me | Theorems.Thm_AggCG_Supplement_theorem_4_3
-- name    : AggCG.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:27:58.219946+00:00
-- url     : https://prove2.me/theorems/a26c7dea-b5e6-4d8f-9437-8a64ebae3d11
-- title:
--   Theorem 4.3 — polynomial-bit Mairal–Yu Lasso path
-- statement:
--   For $p\ge1$, set $B=100p^3$, $a_j=B^{-(j-1)}$, $y=\mathbf1_p$, and let $X$ be upper triangular with $X_{jj}=a_j$ and $X_{ij}=2a_j$ for $i<j$. Every leading $j\times j$ instance has no positive Lasso kink below $a_j/[2(2j-1)^2]$, while the full path has exactly
--
--   $$
--   \frac{3^p+1}{2}
--   $$
--
--   sign-pattern segments. The input has polynomial bit length, and $\lambda_0=a_p/[4(2p-1)^2]$ is a positive polynomial-bit cutoff below every kink.
--
--   Differences from the source:
--   - encoding: polynomial bit length → uniform constants $c,e$ bound the lengths of the self-delimiting binary encodings by $c(p+1)^e$; reason: this is an explicit Turing-model rendering of the same polynomial-bit claim
-- source:
--   Sharma, STOC 2027 submission (manuscript sha256 f7ea0248…), Theorem 4.3, p.5, PDF p.6

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_AggCG_Supplement_lassoPath

namespace AggCG.Supplement

/-- **Theorem 4.3** (Polynomial-bit Mairal–Yu path; Sharma, *Computational Complexity of Data-Driven
Configuration for Integer Programming, Clustering, and Learning Algorithms*, STOC 2027 submission
(manuscript sha256 f7ea0248…), p.5, PDF p.6). For `p ≥ 1` let `B = 100p³`, `a_j = B^{−(j−1)}`,
`y = 1_p`, and `X_{ij} = 0` for `i > j`, `X_{jj} = a_j`, `X_{ij} = 2a_j` for `i < j`
(`mairalYu (100 p³) p`). Then:
(1) for every `1 ≤ j ≤ p`, the `j`-dimensional truncated instance (leading `j × j` block, `y = 1_j`) has no
positive Lasso kink below `a_j/[2(2j − 1)²]`;
(2) the full `p`-dimensional path has exactly `(3^p + 1)/2` sign-pattern segments;
(3) its input has polynomial bit length, and `λ₀ = a_p/[4(2p − 1)²]` is a positive polynomial-bit
cutoff below every kink of the full path; the polynomial is one for all `p`.

**Formalization Note** Bit lengths are the lengths of the self-delimiting binary codes of the rational
entries, summed over the matrix. -/
theorem theorem_4_3 :
    ∃ c e : ℕ, ∀ p : ℕ, 1 ≤ p →
      let B : ℚ := 100 * (p : ℚ) ^ 3
      let a : ℕ → ℚ := fun j => (B ^ (j - 1))⁻¹
      let X : Matrix (Fin p) (Fin p) ℝ := (mairalYu B p).map ((↑) : ℚ → ℝ)
      let lam0 : ℚ := a p / (4 * (2 * (p : ℚ) - 1) ^ 2)
      (∀ j : ℕ, 1 ≤ j → j ≤ p → ∀ lam : ℝ, 0 < lam → lam < ((a j / (2 * (2 * (j : ℚ) - 1) ^ 2) : ℚ) : ℝ) →
        ¬ IsKink (lassoPath ((mairalYu B j).map ((↑) : ℚ → ℝ)) (fun _ => 1)) lam) ∧
      signSegmentCount (lassoPath X (fun _ => 1)) = ((3 ^ p + 1) / 2 : ℕ) ∧
      (∑ i : Fin p, ∑ k : Fin p, (QAlgorithms.LocalHamiltonian.encRat (mairalYu B p i k)).length) ≤
        c * (p + 1) ^ e ∧
      0 < lam0 ∧ (QAlgorithms.LocalHamiltonian.encRat lam0).length ≤ c * (p + 1) ^ e ∧
      ∀ lam : ℝ, IsKink (lassoPath X (fun _ => 1)) lam → (lam0 : ℝ) < lam := by sorry

end AggCG.Supplement
