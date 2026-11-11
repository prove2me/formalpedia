-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_4
-- name    : DetSpectralSparsify.Dense.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:12.317303+00:00
-- url     : https://prove2.me/theorems/45eb8f58-7bb8-4a86-8a7e-d7509a5ec6cb
-- title:
--   Lemma 4 (Chord bounds for the exponential) — e^{θX} ⪯ I + (e^θ − 1)X for 0 ⪯ X ⪯ I
-- statement:
--   Let $X$ be a real symmetric $r\times r$ matrix with $0\preceq X\preceq I$. Then for every $\theta\in\mathbb R$,
--   $$e^{\theta X}\;\preceq\;I+(e^\theta-1)X .$$
--
--   Applied with $\theta=\theta_+>0$ and $\theta=-\theta_-<0$ it gives the one-step bounds of the matrix Chernoff estimator.
--
--   **Formalization Note** $0\preceq X$ is `X.PosSemidef` (which includes symmetry) and $X\preceq I$ is `PSDLe X 1`; $e^{\theta X}$ is the matrix exponential `NormedSpace.exp`.
--
--   Differences from the source: none.
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.5, Lemma 4

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 4 (Chord bounds for the exponential), p.5. If `0 ⪯ X ⪯ I` then for every real `θ`,
`e^{θX} ⪯ I + (e^θ - 1) X`. -/
theorem lemma_4 {r : ℕ} (X : Matrix (Fin r) (Fin r) ℝ) (hX0 : X.PosSemidef)
    (hX1 : PSDLe X 1) (θ : ℝ) :
    PSDLe (NormedSpace.exp (θ • X)) (1 + (Real.exp θ - 1) • X) := by sorry

end DetSpectralSparsify.Dense
