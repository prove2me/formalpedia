-- Prove2me | Theorems.Thm_ErdosRenyiLSC_Main_lemma_6_1
-- name    : ErdosRenyiLSC.Main.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:19:45.01817+00:00
-- url     : https://prove2.me/theorems/aca5b883-e4ed-439e-baf7-00975c2b55b5
-- title:
--   Lemma 6.1, p. 57 — interlacing of the eigenvalues of H and A = H + f|e⟩⟨e|
-- statement:
--   Let $H$ be a real symmetric $N\times N$ matrix, $f\ge0$, $e=N^{-1/2}(1,\dots,1)^T$ and $A=H+f|e\rangle\langle e|$. Let $\lambda_1\le\dots\le\lambda_N$ be the eigenvalues of $H$ and $\mu_1\le\dots\le\mu_N$ those of $A$, counted with multiplicity. Then
--   $$\lambda_1\le\mu_1\le\lambda_2\le\mu_2\le\cdots\le\mu_{N-1}\le\lambda_N\le\mu_N .$$
--
--   Interlacing transfers the counting function of $H$ to that of $A$ up to an error $1/N$; this is the input for the trace comparison of Lemma 7.1.
--
--   **Formalization Note** Indices are zero-based: the statement is $\lambda_k\le\mu_k$ for $0\le k\le N-1$ and $\mu_k\le\lambda_{k+1}$ for $0\le k\le N-2$. The $k$-th eigenvalue is the $k$-th smallest root of the characteristic polynomial. The statement holds for every real symmetric $H$; $f\ge0$ is condition (2.8).
-- source:
--   Erdős, Knowles, Yau and Yin, Spectral statistics of Erdős–Rényi graphs I: Local semicircle law, arXiv:1103.1919v5, p. 57, Lemma 6.1, (6.1)

import Mathlib
import Definitions.Def_ErdosRenyiLSC_Main_Setting
import Definitions.Def_ErdosRenyiLSC_Main_Resolvent

noncomputable section

namespace ErdosRenyiLSC.Main

/-- Lemma 6.1, p. 57: the eigenvalues `λ₁ ≤ ⋯ ≤ λ_N` of `H` and `μ₁ ≤ ⋯ ≤ μ_N` of
`A = H + f|e⟩⟨e|` interlace, `λ₁ ≤ μ₁ ≤ λ₂ ≤ μ₂ ≤ ⋯ ≤ μ_{N-1} ≤ λ_N ≤ μ_N`
(zero-based indices `k = 0, …, N-1`). -/
theorem lemma_6_1 {N : ℕ} (H : Matrix (Fin N) (Fin N) ℝ)
    (hsymm : ∀ i j : Fin N, H i j = H j i) (f : ℝ) (hf : 0 ≤ f) :
    (∀ k : ℕ, k < N → eigAsc H k ≤ eigAsc (H + f • proj N) k) ∧
    (∀ k : ℕ, k + 1 < N → eigAsc (H + f • proj N) k ≤ eigAsc H (k + 1)) := by sorry

end ErdosRenyiLSC.Main
