-- Prove2me | Theorems.Thm_AddXnor_Supplement_theorem_5
-- name    : AddXnor.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T01:33:09.673668+00:00
-- url     : https://prove2.me/theorems/75b00c4f-3608-47be-991d-19479f610980
-- title:
--   Theorem 5 — Spectrum of single-bit approximations
-- statement:
--   Fix $1\le j\le m-1$, let $M_j[s',s]=(-1)^{[s'<s]}$ on $N=2^j$ states, and put
--   $$
--   \lambda_k=1-i\cot\frac{(2k+1)\pi}{2^{j+1}},\qquad
--   \rho_j=\frac1{2^j\sin(\pi/2^{j+1})}.
--   $$
--   The bit-$j$ correlation factors over addition runs as $\prod_t c_j(z_t)$; $M_j$ is diagonalizable with the displayed eigenvalues; and
--   $$
--   c_j(z)=2^{-j(z+2)}\sum_{k=0}^{N-1}|\lambda_k|^2\lambda_k^z,qquad |c_j(z)|\le\rho_j^z.
--   $$
--   Finally $\rho_1=2^{-1/2}>\rho_2>\rho_3>\cdots$, $\rho_j\to2/\pi$, and $|c_j(z)|\le2^{-z/2}$, with the stated equality case at $j=1$ and $z\equiv0\pmod4$.
--
--   Differences from the source:
--   - encoding: diagonalizable with indexed eigenvalues → existence of an eigenvector matrix with nonzero determinant whose columns have exactly those indexed eigenvalues; reason: this is the finite-dimensional complex definition of the same claim
--   - encoding: uniform random operands and signed correlations → exact finite averages over `BitVec` operands; reason: finite-type encoding with identical uniform weights
-- source:
--   Wang, Lv, Shen, Zhang, manuscript (sha256 405d6dda…), Theorem 5, pp.17–18 (PDF pp.17–18)

import Mathlib
import Definitions.Def_AddXnor_Supplement_core

set_option autoImplicit false

namespace AddXnor.Supplement

/-- **Theorem 5 (Spectrum of single-bit approximations)** (Wang, Lv, Shen, Zhang,
*Add/XNOR Chains*, manuscript, sha256 405d6dda..., Theorem 5, pp.17--18
(PDF pp.17--18)).

All four printed clauses are retained: run-factorization, the indexed eigenbasis and exact
spectral sum, the `ρ_j` bound, and the strict decay-rate comparison with its limit and equality
case.  Bit indices are least-significant first. -/
theorem theorem_5 (m j : ℕ) (hj : 1 ≤ j) (hjm : j ≤ m - 1) :
    (∀ (q : ℕ), 1 ≤ q → ∀ x : Fin q → Bool,
      correlationAt (m := m) x j =
        ((additionRuns x).map (carryCorrelation j)).prod) ∧
    HasIndexedEigenbasis (transferMatrix j) (eigenvalue j) ∧
    (∀ z : ℕ,
      (carryCorrelation j z : ℂ) =
        (Real.rpow 2 (-((j * (z + 2) : ℕ) : ℝ)) : ℂ) *
          ∑ k : Fin (2 ^ j),
            ((‖eigenvalue j k‖ : ℝ) ^ 2) * (eigenvalue j k) ^ z) ∧
    (∀ z : ℕ, |carryCorrelation j z| ≤ (rho j) ^ z) ∧
    rho 1 = Real.rpow 2 (-(1 : ℝ) / 2) ∧
    (∀ a : ℕ, 1 ≤ a → rho (a + 1) < rho a) ∧
    Filter.Tendsto rho Filter.atTop (nhds (2 / Real.pi)) ∧
    (∀ (a z : ℕ), 1 ≤ a →
      |carryCorrelation a z| ≤ Real.rpow 2 (-(z : ℝ) / 2)) ∧
    (∀ z : ℕ, z % 4 = 0 →
      |carryCorrelation 1 z| = Real.rpow 2 (-(z : ℝ) / 2)) := by sorry

end AddXnor.Supplement
