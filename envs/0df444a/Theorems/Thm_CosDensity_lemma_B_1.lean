-- Prove2me | Theorems.Thm_CosDensity_lemma_B_1
-- name    : CosDensity.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:37:44.358509+00:00
-- url     : https://prove2.me/theorems/cf0c3641-3467-4f56-855f-7c5454750e0e
-- title:
--   Lemma B.1 — $\mathbb E|A\cap B|^p\le C_p s^2/m$ for random $s$-subsets
-- statement:
--   Let $A$ and $B$ be independent uniformly random $s$-subsets of $[m]$ and let $X=|A\cap B|$. For every integer $p\ge 1$ there is a constant $C_p>0$, depending only on $p$, such that whenever $m\ge 2p$ and $s^2/m\le 1$,
--
--   $$\mathbb E[X^p]\le C_p\,\frac{s^2}{m}.$$
--
--   This moment bound controls the $p$-th power correlations of random sparse codewords in Lemma 8.2.
--
--   Differences from the source:
--   - encoding: expectation over independent uniform s-subsets A, B of [m] → the average of |A ∩ B|^p over all pairs of s-subsets of Fin m; reason: the uniform product law; the hypotheses force 1 ≤ m and s ≤ m, so the average is over a nonempty set
-- source:
--   Q. Zhang, Frequency Moments Beyond Equality: Streaming Cosine Density Moments, arXiv:2609.06925 (held version, sha256 f4d4df22…), Appendix B.1, Lemma B.1, p.41 (pdf_page 42)

import Mathlib

namespace CosDensity

/-- **Lemma B.1** (sparse-intersection moment bound). Q. Zhang, *Frequency Moments Beyond
Equality: Streaming Cosine Density Moments*, arXiv:2609.06925 (held version, sha256 f4d4df22…),
Appendix B.1, Lemma B.1, p.41 (pdf_page 42).

Let `A`, `B` be independent uniformly random `s`-subsets of `[m]` and `X = |A ∩ B|`. For every
integer `p ≥ 1` there is `C_p > 0` such that `E[X^p] ≤ C_p s²/m` whenever `m ≥ 2p` and
`s²/m ≤ 1`.

**Formalization Note.** `[m]` is `Fin m`; the expectation over the independent uniform pair is the
average of `|A ∩ B|^p` over all pairs of `s`-subsets. The hypotheses force `1 ≤ m` and `s ≤ m`, so
there are `s`-subsets. The constant is chosen before `m` and `s`. -/
theorem lemma_B_1 (p : ℕ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ m s : ℕ, 2 * p ≤ m → (s : ℝ) ^ 2 / m ≤ 1 →
      (((Finset.univ : Finset (Fin m)).powersetCard s).card : ℝ)⁻¹ ^ 2 *
          ∑ A ∈ (Finset.univ : Finset (Fin m)).powersetCard s,
            ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard s, ((A ∩ B).card : ℝ) ^ p ≤
        C * ((s : ℝ) ^ 2 / m) := by sorry

end CosDensity
