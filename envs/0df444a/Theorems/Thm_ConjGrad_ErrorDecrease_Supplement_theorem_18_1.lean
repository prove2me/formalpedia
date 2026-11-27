-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_18_1
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_18_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-24T02:05:24.675223+00:00
-- url     : https://prove2.me/theorems/9d8a2bdd-057d-4adc-b3ab-7e105d94b56a
-- title:
--   Theorem 18:1 — the cg numbers $a_i,b_i$ from the continued fraction of $Q_{n-1}/\det(\lambda I-A)$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix with characteristic polynomial $\chi(\lambda)=\det(\lambda I-A)$, and run the cg-method from $x_0$ with $r_0=k-Ax_0$ not perpendicular to any eigenvector of $A$ (the setting of §18: distinct eigenvalues and positive weights). Let $Q_{n-1}(\lambda)=r_0^{\mathsf T}\operatorname{adj}(\lambda I-A)r_0$ be the characteristic polynomial of $A$ with respect to $r_0$, and $F=Q_{n-1}/\chi$. With the cg numbers $a_i$ and $c_0=0$, $c_i=b_{i-1}a_i/a_{i-1}$ (15:4), let $N_i/R_i$ be the convergents of the continued fraction (18:2) normalized by $d_i=1+c_i$. Then
--
--   $$R_n=\frac{\chi}{\chi(0)},\qquad Q_{n-1}R_n=\kappa\,N_n\,\chi\quad\text{with }\kappa=a_0|r_0|^2,$$
--
--   i.e. $F=\kappa N_n/R_n$; the $b_i$ are recovered by $b_i=c_{i+1}a_i/a_{i+1}$ ($i+1<n$); and the expansion is unique: if numbers $a_i'\ne0$ ($i<n$), $c_i'$ and $\kappa'$ satisfy $Q_{n-1}R'_n=\kappa'N'_n\chi$, then $a_i'=a_i$ ($i<n$), $c_i'=c_i$ ($0<i<n$) and, for $n>0$, $\kappa'=\kappa$.
--
--   The final coefficient is $b_{n-1}=0$ when $n>0$.
--
--   The theorem recovers the complete sequence of cg coefficients from spectral data alone, and is the basis of Theorem 18:3.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - reading: “can be computed by expanding $F$ into a continued fraction” → the identity $Q_{n-1}R_n=\kappa N_n\chi$ with the cg coefficients, $R_n=\chi/\chi(0)$, recovery of $b_i$ by (15:4), and uniqueness of the normalized expansion; reason: this is what computing the numbers by the expansion means; the scalar $\kappa$ accounts for the numerator $-1$ of (18:2) against the normalization of $F$
--   - encoding: “distinct eigenvalues, positive weights $m_j$” (type (b) of §18) → $r_0$ not perpendicular to any eigenvector; reason: for symmetric $A$ this is equivalent: it gives $m_j=(r_0,e_j)^2>0$ and forces distinct eigenvalues
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 432, Theorem 18:1 with (18:1)–(18:3), (15:2), (15:4) (PDF p. 24)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_cfConv
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:1 (Hestenes–Stiefel 1952, p. 432): for symmetric positive definite `A` and an
initial residual `r₀ = k − Ax₀` not perpendicular to any eigenvector, the cg numbers `aᵢ`, `bᵢ`
are obtained by expanding `F = Q/χ` (`Q` the characteristic polynomial of `A` with respect to
`r₀`, `χ` the characteristic polynomial of `A`) into the normalized continued fraction (18:2):
`F = κ Nₙ/Rₙ` with `κ = a₀|r₀|²`, `Rₙ = χ/χ(0)`, `bᵢ = cᵢ₊₁aᵢ/aᵢ₊₁` (15:4), and these
coefficients are the only ones giving such an expansion. -/
theorem theorem_18_1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ)
    (hcyc : ∀ (v : Fin n → ℝ) (c : ℝ), v ≠ 0 → A *ᵥ v = c • v →
      (cgIter A k x₀ 0).r ⬝ᵥ v ≠ 0) :
    (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
        Polynomial.C (A.charpoly.eval 0)⁻¹ * A.charpoly ∧
    relCharPoly A (cgIter A k x₀ 0).r * (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).2 =
      Polynomial.C (cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) *
        (cfConv (fun i => cgAlpha A (cgIter A k x₀ i)) (cgCoeffC A k x₀) n).1 * A.charpoly ∧
    (∀ i : ℕ, i + 1 < n →
      ((cgIter A k x₀ (i + 1)).r ⬝ᵥ (cgIter A k x₀ (i + 1)).r) /
          ((cgIter A k x₀ i).r ⬝ᵥ (cgIter A k x₀ i).r) =
        cgCoeffC A k x₀ (i + 1) * cgAlpha A (cgIter A k x₀ i) /
          cgAlpha A (cgIter A k x₀ (i + 1))) ∧
    (0 < n → cgBeta A k x₀ (n - 1) = 0) ∧
    (∀ (a c : ℕ → ℝ) (κ : ℝ), (∀ i < n, a i ≠ 0) →
      relCharPoly A (cgIter A k x₀ 0).r * (cfConv a c n).2 = Polynomial.C κ * (cfConv a c n).1 * A.charpoly →
      (0 < n → κ = cgAlpha A (cgIter A k x₀ 0) * ((cgIter A k x₀ 0).r ⬝ᵥ (cgIter A k x₀ 0).r)) ∧
      (∀ i < n, a i = cgAlpha A (cgIter A k x₀ i)) ∧
      ∀ i : ℕ, 0 < i → i < n → c i = cgCoeffC A k x₀ i) := by sorry

end ConjGrad.ErrorDecrease.Supplement
