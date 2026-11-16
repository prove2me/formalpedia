-- Prove2me | Theorems.Thm_BLTCounting_AccuracySpace_Supplement_lemma_3_5
-- name    : BLTCounting.AccuracySpace.Supplement.lemma_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:00:31.376294+00:00
-- url     : https://prove2.me/theorems/486a8e70-4537-4b25-9d00-709fa0e5000a
-- title:
--   Lemma 3.5 — Eigenvalue transfer under diagonal normalization
-- statement:
--   Let $m\ge2$ and $\gamma\in(0,1]$, and construct $H_S$ and $\widetilde H_S$ on the Section 3 lattice. Both matrices are Hermitian, and their eigenvalues, ordered nonincreasingly with multiplicity, satisfy
--   $$\lambda_j(H_S)\ge m^{-1/2}\lambda_j(\widetilde H_S)\qquad(1\le j\le K).$$
--   This transfers the normalized eigenvalue count to the original principal submatrix.
--
--   Differences from the source:
--   - encoding: ordered eigenvalues of the real symmetric constructed matrices → Hermitian witnesses in the conclusion and zero-based eigenvalue indices; reason: real symmetric matrices are complex Hermitian; all K eigenvalues and multiplicities are unchanged
-- source:
--   Monika Henzinger, Jalaj Upadhyay, Lower Bounds for Memory-Efficient Differentially Private Continual Counting, STOC 2027 submission #357 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/357.pdf, SHA-256 4bc286dfed41ddf6b1f9ec058dd7964f530cf194be79fa5d9dd129d4ae37d510, Lemma 3.5, printed p. 16 (PDF p. 17)

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_Supplement_Lattice

namespace BLTCounting.AccuracySpace.Supplement

/-- Lemma 3.5, PDF p.17. Hermiticity of the constructed matrices is a conclusion, not a hypothesis.
The index j is the source's j+1; the eigenvalues have multiplicity and descend. -/
theorem lemma_3_5 (m : ℕ) (hm : 2 ≤ m) (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ hH : (latticeHankel m γ).IsHermitian,
    ∃ hT : (normalizedHankel m γ).IsHermitian,
      ∀ j : ℕ, j < latticeK m γ →
        (m : ℝ) ^ (-(1 / 2 : ℝ)) * eigAt hT j ≤ eigAt hH j := by sorry

end BLTCounting.AccuracySpace.Supplement
