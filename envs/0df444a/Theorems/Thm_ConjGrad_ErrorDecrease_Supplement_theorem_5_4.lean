-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_5_4
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:56:34.658862+00:00
-- url     : https://prove2.me/theorems/fe0c3b4a-3c99-425d-b43f-a2c66308eb7e
-- title:
--   Theorem 5:4 — three-term recurrences (5:7) for directions and (5:8) for residuals
-- statement:
--   For the cg-method with a real symmetric positive definite $A$, scalars $a_i=|r_i|^2/(p_i,Ap_i)$ and $b_i=|r_{i+1}|^2/|r_i|^2$:
--
--   $$p_1=(1+b_0)p_0-a_0Ap_0,\qquad p_{i+1}=(1+b_i)p_i-a_iAp_i-b_{i-1}p_{i-1}\ (i>0), \tag{5:7}$$
--
--   $$r_1=r_0-a_0Ar_0,\qquad r_{i+1}=(1+b'_{i-1})r_i-a_iAr_i-b'_{i-1}r_{i-1}, \tag{5:8}$$
--
--   where $b'_{i-1}=(a_i/a_{i-1})\,b_{i-1}$ (5:9).
--
--   The recurrences eliminate one of the two vector sequences and connect the cg-method with three-term recurrences of orthogonal polynomials (§§14–15).
--
--   **Formalization Note** Vectors are `Fin n → ℝ` with the dot product $(x,y)=\sum_l x_ly_l$ and $|z|^2=(z,z)$. The cg-method is the published iteration `cgIter` of (5:1), 0-based, with no stopping test: once $r_m=0$ Lean's convention $t/0=0$ keeps $x_i=h$ and $r_i=p_i=0$ for $i\ge m$. $A$ is real, symmetric and positive definite (`A.PosDef`), the paper's standing assumption on p. 410. The integer $m$ is the step at which the cg-method terminates: $r_m=0$ and $r_j\neq0$ for $j<m$ (the paper's $x_m=h$; such an $m\le n$ exists by Theorem 4:2, so these hypotheses exclude no run).
--
--   Differences from the source:
--   - generalization: statements about the run $x_0,\dots,x_m$ of the cg-method → the identities are asserted for every index $i$, including $i>m$ where Lean's $t/0=0$ gives $x_i=h$, $r_i=p_i=0$; reason: on $i\le m$ they are the source's statements; beyond $m$ both sides take the same totalized values
--   - encoding: the paper's step index $i\ge1$ → Lean index $i+1$ with $i\ge0$; reason: avoids natural-number subtraction; same instances
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 415, Theorem 5:4, eqs. (5:7a)–(5:9) (PDF p. 7)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 5:4 (Hestenes–Stiefel 1952, p. 415): the three-term recurrences (5:7a)–(5:8b) with
`bᵢ₋₁' = (aᵢ/aᵢ₋₁)bᵢ₋₁` (5:9). (5:7b) and (5:8b) are stated at the paper's index `i + 1 > 0`. -/
theorem theorem_5_4 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (k x₀ : Fin n → ℝ) :
    (cgIter A k x₀ 1).p = (1 + cgBeta A k x₀ 0) • (cgIter A k x₀ 0).p -
      cgAlpha A (cgIter A k x₀ 0) • (A *ᵥ (cgIter A k x₀ 0).p) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 2)).p =
      (1 + cgBeta A k x₀ (i + 1)) • (cgIter A k x₀ (i + 1)).p -
        cgAlpha A (cgIter A k x₀ (i + 1)) • (A *ᵥ (cgIter A k x₀ (i + 1)).p) -
        cgBeta A k x₀ i • (cgIter A k x₀ i).p) ∧
    (cgIter A k x₀ 1).r = (cgIter A k x₀ 0).r -
      cgAlpha A (cgIter A k x₀ 0) • (A *ᵥ (cgIter A k x₀ 0).r) ∧
    (∀ i : ℕ, (cgIter A k x₀ (i + 2)).r =
      (1 + cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) * cgBeta A k x₀ i) •
          (cgIter A k x₀ (i + 1)).r -
        cgAlpha A (cgIter A k x₀ (i + 1)) • (A *ᵥ (cgIter A k x₀ (i + 1)).r) -
        (cgAlpha A (cgIter A k x₀ (i + 1)) / cgAlpha A (cgIter A k x₀ i) * cgBeta A k x₀ i) •
          (cgIter A k x₀ i).r) := by sorry

end ConjGrad.ErrorDecrease.Supplement
