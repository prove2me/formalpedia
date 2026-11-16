-- Prove2me | Theorems.Thm_DenseLanguageGeneration_PatientScope_Supplement_low_crossing_partition
-- name    : DenseLanguageGeneration.PatientScope.Supplement.low_crossing_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:37.411719+00:00
-- url     : https://prove2.me/theorems/da8aed8c-33ca-469a-b856-66636421367a
-- title:
--   Theorem 2.5 — Low-crossing partition
-- statement:
--   Let $s,m,k$ be positive integers with $s\mid m$, and let $\sigma_1,\ldots,\sigma_k$ be permutations of $[m]$, read as sequences. There is a balanced partition $G_1,\ldots,G_{m/s}$ into groups of exactly $s$ elements such that its crossing numbers satisfy
--
--   $$c_i(n)\le4\left(\frac ms\right)^{1-1/k}\qquad(i\in[k],\ 1\le n\le m).$$
--
--   A group is crossed if it meets both the prefix $[n]_i$ and its complement. The same partition works for every order and prefix. This companion theorem provides the finite partition guarantee used by the paper's multiple-order algorithms; it is not a step of the retained goal's proof.
--
--   Differences from the source:
--   - encoding: groups and elements labelled from one, and a positive number of orders → Fin m elements, Fin (m / s) group labels, Fin k orders and 1 ≤ k; reason: adding one preserves every permutation, cut and partition; a positive k is the domain of the displayed exponent
--   - encoding: a labelled partition into m/s disjoint groups of size s covering [m] → the published total bucket map Fin m → Fin (m / s) with every fibre of size s; reason: its fibres form exactly the source partition; every labelled source partition determines the unique label of each element, and the reused predicate has no extra assumptions
-- source:
--   Ziyi Cai, Shuangping Li, Yiheng Shen, Kangning Wang and Peng Zhang, Dense Language Generation Made Simple: Deterministic, Randomized, and Multi-Order Algorithms, STOC 2027 submission #335 (October 2026), Theorem 2.5, printed p.9 (PDF p.11); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/335.pdf

import Definitions.Def_DenseLanguageGeneration_PatientScope_Supplement_lowCrossing

set_option autoImplicit false

namespace DenseLanguageGeneration.PatientScope.Supplement

/-- Cai et al., STOC 2027 submission #335 (October 2026), Theorem 2.5,
printed p.9 (PDF p.11); proof in Appendix A, printed p.39 (PDF p.41).
[m] is `Fin m` (zero-based); the bound is the real power 4·(m/s)^(1−1/k),
for every order i and every prefix length 1 ≤ n ≤ m. -/
theorem low_crossing_partition (s m k : ℕ) (hs : 0 < s) (hm : 0 < m) (hsm : s ∣ m) (hk : 1 ≤ k)
    (σ : Fin k → Equiv.Perm (Fin m)) :
    ∃ b : Fin m → Fin (m / s), QCollLB.IsBucketMap s b ∧
      ∀ (i : Fin k) (n : ℕ), 1 ≤ n → n ≤ m →
        (crossingNumber b (σ i) n : ℝ) ≤ 4 * ((m : ℝ) / (s : ℝ)) ^ (1 - 1 / (k : ℝ)) := by sorry

end DenseLanguageGeneration.PatientScope.Supplement
