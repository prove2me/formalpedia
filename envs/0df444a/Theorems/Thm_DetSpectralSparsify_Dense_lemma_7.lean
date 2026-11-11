-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_7
-- name    : DetSpectralSparsify.Dense.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:11.869294+00:00
-- url     : https://prove2.me/theorems/7d493f02-b4c4-4cc1-a467-9230024b8361
-- title:
--   Lemma 7 (Perturbation of a negative exponential) — ‖e^{−A} − e^{−B}‖ ≤ ‖A − B‖ for A, B ⪰ 0
-- statement:
--   Let $A,B$ be real symmetric positive semidefinite $r\times r$ matrices. Then
--   $$\big\|e^{-A}-e^{-B}\big\|\;\le\;\|A-B\|,$$
--   where $\|\cdot\|$ is the operator norm.
--
--   The bound converts approximation errors in the exponents $Q_{\pm,j}$ into errors of the estimator matrices in both score implementations.
--
--   **Formalization Note** The operator norm is `opNorm`, the norm of the matrix acting on Euclidean space.
--
--   Differences from the source:
--   - encoding: ∥·∥ the operator norm → `opNorm M = ‖toEuclideanCLM M‖`; reason: the ℓ²→ℓ² operator norm in Mathlib's form
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.12, Lemma 7

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 7 (Perturbation of a negative exponential), p.12. If `A, B ⪰ 0` then
`‖e^{-A} - e^{-B}‖ ≤ ‖A - B‖` in operator norm. -/
theorem lemma_7 {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    opNorm (NormedSpace.exp (-A) - NormedSpace.exp (-B)) ≤ opNorm (A - B) := by sorry

end DetSpectralSparsify.Dense
