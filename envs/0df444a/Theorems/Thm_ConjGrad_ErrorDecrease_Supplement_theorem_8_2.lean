-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_8_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_8_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:03:17.66075+00:00
-- url     : https://prove2.me/theorems/7b66ed90-bac2-4d8f-ae6c-0af0cf8ea7f5
-- title:
--   Theorem (§8.2, unnumbered) — a starting residual with stability ratios $a_i/a_{i-1}<1$
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix with distinct eigenvalues and $k\in\mathbb R^n$. There is an initial estimate $x_0$ — equivalently an initial residual $r_0=k-Ax_0$ — such that the cg-method takes $n$ active steps ($r_i\ne0$ for $i<n$) and
--
--   $$\frac{a_i}{a_{i-1}}<1\qquad(i=1,\dots,n-1),$$
--
--   so that the algorithm is stable with respect to the propagation of rounding-off errors in the sense of §8.2.
--
--   In §8.2 the ratio $a_i/a_{i-1}$ is the factor by which the conjugacy defect $(Ap_i,p_{i+1})/(Ap_i,p_i)$ propagates (8:10b); a ratio below one is the paper's stability criterion, and the theorem says it can always be achieved by choosing the start.
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410.
--
--   Differences from the source:
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
--   - reading: “stable with respect to the propagation of rounding-off errors” → the criterion $a_i/a_{i-1}<1$ for $1\le i\le n-1$ along an $n$-step run; reason: the paragraph before the theorem defines stability by this ratio; no floating-point model is part of the claim
--   - reading: “there exists an initial residual vector $r_0$” → for every $k$ there is $x_0$ with that residual behaviour; reason: $A$ is invertible, so every $r_0$ is $k-Ax_0$ for a unique $x_0$
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 421, §8.2, unnumbered theorem (PDF p. 13)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- The unnumbered theorem of §8.2 (Hestenes–Stiefel 1952, p. 421): for a symmetric positive
definite `A` with distinct eigenvalues there is an initial residual `r₀ = k − Ax₀` for which the
cg-method takes `n` active steps and the stability ratios satisfy `aᵢ/aᵢ₋₁ < 1`
(`1 ≤ i ≤ n − 1`), stated at the paper's index `i + 1`. -/
theorem theorem_8_2 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (hdist : Function.Injective hA.1.eigenvalues) (k : Fin n → ℝ) :
    ∃ x₀ : Fin n → ℝ, (∀ i < n, (cgIter A k x₀ i).r ≠ 0) ∧
      ∀ i : ℕ, i + 1 < n →
        cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) < 1 := by sorry

end ConjGrad.ErrorDecrease.Supplement
