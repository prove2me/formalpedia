-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_18_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_18_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:05:56.501921+00:00
-- url     : https://prove2.me/theorems/a4f89062-39ae-44eb-bb8d-2a37d09b7c6b
-- title:
--   Theorem 18:2 — with $r_0=\sum e_j$ the cg numbers come from the continued fraction of $\chi'/\chi$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix with orthonormal eigenvectors $e_1,\dots,e_n$, $Ae_j=\lambda_je_j$, distinct eigenvalues, and characteristic polynomial $\chi$. If the initial residual of a cg-process is $r_0=k-Ax_0=e_1+\cdots+e_n$, then the characteristic polynomial of $A$ with respect to $r_0$ is $\chi'$, so $F=\chi'/\chi$ is the logarithmic derivative of $\chi$, and the cg numbers are obtained by expanding it into the normalized continued fraction (18:2): with $N_i/R_i$ as in Theorem 18:1,
--
--   $$R_n=\frac{\chi}{\chi(0)},\qquad \chi'\,R_n=\kappa\,N_n\,\chi\quad(\kappa=a_0|r_0|^2),$$
--
--   $b_i=c_{i+1}a_i/a_{i+1}$ for $i+1<n$, and the expansion is unique as in Theorem 18:1.
--
--   The final coefficient is $b_{n-1}=0$ when $n>0$.
--
--   This is the special case $m_1=\cdots=m_n=1$ of Theorem 18:1.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - reading: “can be computed by expanding the logarithmic derivative into a continued fraction” → as in Theorem 18:1 with $Q_{n-1}=\chi'$; reason: same reading as Theorem 18:1
--   - reading: “the sum of the normalized eigenvectors” → any orthonormal eigenbasis $e_j$ (signs arbitrary); reason: the normalized eigenvectors are determined up to sign; the conclusion holds for every choice
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 432, Theorem 18:2 (PDF p. 24)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cfConv
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:2 (Hestenes–Stiefel 1952, p. 432): if `r₀ = k − Ax₀` is the sum of an orthonormal
system of eigenvectors of `A` with distinct eigenvalues, the characteristic polynomial of `A`
with respect to `r₀` is `χ'`, and the cg numbers are obtained by expanding the logarithmic
derivative `χ'/χ` into the normalized continued fraction (18:2), uniquely. -/
theorem theorem_18_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) (lam : Fin n → ℝ) (e : Fin n → Fin n → ℝ)
    (horth : ∀ i j, e i ⬝ᵥ e j = if i = j then 1 else 0)
    (heig : ∀ j, A *ᵥ e j = lam j • e j) (hdist : Function.Injective lam)
    (hr : (cgIter A k x₀ 0).r = ∑ j, e j) :
    relCharPoly A (cgIter A k x₀ 0).r = Polynomial.derivative A.charpoly ∧
    (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
        Polynomial.C (A.charpoly.eval 0)⁻¹ * A.charpoly ∧
    Polynomial.derivative A.charpoly * (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
      Polynomial.C (cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) *
        (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).1 * A.charpoly ∧
    (∀ i : ℕ, i + 1 < n →
      ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        cgCoeffC A k x₀ (i + 1) * cgAlpha A (cgIter A k x₀ i) /
          cgAlpha A (cgIter A k x₀ (i + 1))) ∧
    (0 < n → cgBeta A k x₀ (n - 1) = 0) ∧
    (∀ (a c : ℕ → ℝ) (κ : ℝ), (∀ i < n, a i ≠ 0) →
      Polynomial.derivative A.charpoly * (cfConv a c n).2 = Polynomial.C κ * (cfConv a c n).1 * A.charpoly →
      (0 < n → κ = cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) ∧
      (∀ i < n, a i = cgAlpha A (cgIter A k x₀ i)) ∧
      ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i) := by sorry

end ConjGrad.ErrorDecrease.Supplement
