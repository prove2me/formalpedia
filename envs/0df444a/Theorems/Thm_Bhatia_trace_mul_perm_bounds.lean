-- Prove2me | Theorems.Thm_Bhatia_trace_mul_perm_bounds
-- name    : Bhatia.trace_mul_perm_bounds
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-14T01:04:28.173011+00:00
-- url     : https://prove2.me/theorems/d5b47e0a-603b-4886-bc66-9f57f1aaf9a2
-- title:
--   Trace pairing lies between permutation pairings of the spectra
-- statement:
--   For two real symmetric matrices $A,B\in\mathbb{R}^{n\times n}$ with eigenvalues $\lambda_i(A)$ and $\lambda_j(B)$, the Frobenius pairing $\langle A,B\rangle=\operatorname{tr}(AB)$ is always sandwiched between two pairings of the spectra: there is a permutation whose pairing underestimates the trace, and a permutation whose pairing overestimates it,
--
--   $$\min_{\sigma\in S_n}\sum_i \lambda_i(A)\lambda_{\sigma(i)}(B) \;\le\; \operatorname{tr}(AB) \;\le\; \max_{\sigma\in S_n}\sum_i \lambda_i(A)\lambda_{\sigma(i)}(B).$$
--
--   Composed with the rearrangement inequality, the two extremes are the reverse-ordered and like-ordered sums, which is the classical statement
--
--   $$\sum_i \lambda_i(A)\lambda_{n+1-i}(B)\;\le\;\langle A,B\rangle\;\le\;\sum_i\lambda_i(A)\lambda_i(B)$$
--
--   for eigenvalues listed in decreasing order — a member of the von Neumann trace-inequality family.
--
--   **Why this form.** Stating the bounds with an existentially quantified permutation avoids having to sort the eigenvalues, which Mathlib's `IsHermitian.eigenvalues` does not do. The sorted statement follows immediately by applying the rearrangement inequality to each permutation sum.
--
--   **Proof sketch.** Diagonalise both matrices, $A=VD_\lambda V^\top$ and $B=WD_\mu W^\top$. Cyclicity of the trace turns $\operatorname{tr}(AB)$ into $\operatorname{tr}(D_\lambda M D_\mu M^\top)$ with $M=V^\top W$, which expands to $\sum_{i,j}\lambda_i\mu_j M_{ij}^2$. Because $M_{ij}=\langle v_i,w_j\rangle$ for two orthonormal eigenbases, the coefficient matrix $(M_{ij}^2)$ has all row and column sums equal to $1$ by Parseval, so it is doubly stochastic. Birkhoff's theorem writes it as a convex combination of permutation matrices, exhibiting $\operatorname{tr}(AB)$ as a convex combination of the sums $\sum_i\lambda_i\mu_{\sigma(i)}$ — and a convex combination always lies between the least and greatest of the values combined.
-- source:
--   Bhatia 2013, Matrix Analysis, Graduate Texts in Mathematics 169, Springer, Problem III.6.14 (also derivable from the Schur-Horn theorem together with Abel summation; see Marshall, Olkin, Arnold 2011, Inequalities: Theory of Majorization and Its Applications, Theorem 9.B.1 and Theorem 9.B.2). Cited as Lemma 4.12 in Chen, Li 2019, Model-free Nonconvex Matrix Completion, JMLR 20(142), https://arxiv.org/abs/1711.01742 (v3), p. 24, where it is used to absorb the residual term in the proof of Lemma 4.8.

import Mathlib.Analysis.Matrix.Spectrum
open Matrix

theorem Bhatia.trace_mul_perm_bounds {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (∃ σ : Equiv.Perm (Fin n),
        ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i) ≤ (A * B).trace) ∧
      (∃ σ : Equiv.Perm (Fin n),
        (A * B).trace ≤ ∑ i, hA.eigenvalues i * hB.eigenvalues (σ i)) := by sorry
