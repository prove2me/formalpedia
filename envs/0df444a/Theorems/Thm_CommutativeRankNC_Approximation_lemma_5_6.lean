-- Prove2me | Theorems.Thm_CommutativeRankNC_Approximation_lemma_5_6
-- name    : CommutativeRankNC.Approximation.lemma_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:50:45.136887+00:00
-- url     : https://prove2.me/theorems/f8dbf904-b764-4e31-bd98-5aa74bf83173
-- title:
--   Lemma 5.6 — Separate homogeneous linearity
-- statement:
--   Fix the same normalized setting, $A\in\mathcal B$, and $k\ge1$. Every entry of the complete polarization of $\widehat J_k$ has degree one in each entire variable bucket separately:
--
--   $$\deg_{Y^{(i)}}M=1\quad\text{for every supported monomial }M\text{ and every }i\in[k].$$
--
--   The condition is imposed on every entry and every supported monomial. Zero entries satisfy it by the homogeneous-support convention; the assertion is not degree one in every scalar coordinate. This is the full separate homogeneity assertion of the source.
--
--   Differences from the source:
--   - generalization: the positive-dimensional matrix setting → also zero-dimensional matrices and empty generating lists; reason: the zero matrix and empty blocks supply these extra cases without excluding any source instance
--   - encoding: the same invertible row and column transformations applied to A and all directions → Normalization data containing rational matrix units, the rank, and the diagonal identity; reason: the normalized matrices are the source objects; they are analysis data and never input advice to the headline algorithm
--   - encoding: one-based matrix and variable indices → zero-based finite index types and ordered pairs for truncated blocks; reason: the same entries and blocks are present under a bijective reindexing
--   - encoding: homogeneous of degree one in a variable group → every supported monomial has total exponent one across that group; reason: this is the standard homogeneous-polynomial convention and includes zero entries
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), Lemma 5.6, PDF/printed p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_Schur

namespace CommutativeRankNC.Approximation

/-- Lemma 5.6, PDF/printed p.25, with separate degree in a whole bucket,
not in every scalar coordinate. Zero entries use the support convention. -/
theorem lemma_5_6 {n m : ℕ} (B : Fin m → QMatrix n) (A : QMatrix n)
    (hA : A ∈ matrixSpace B) (S : Normalization A) (k : ℕ) (hk : 0 < k) :
    ∀ u v bucket, BucketLinear (polarizedJ S B k u v) bucket := by sorry

end CommutativeRankNC.Approximation
