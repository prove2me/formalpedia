-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_corollary_3_7
-- name    : CorrBoundsPoly.ExactDegree.corollary_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:58:58.771166+00:00
-- url     : https://prove2.me/theorems/67d76ef4-62c8-475e-8c73-20c647afecbf
-- title:
--   Corollary 3.7 — $\rho_{D-1}(\sigma_{D,m})\le a_D(m)\le\frac32e^{-m/D^2}$; blocks give $e^{-n/(2D^2)}$, and $\rho_d\le e^{-n/(8d^2)}$
-- statement:
--   Let $D\ge2$ be dyadic.
--   1. For all $m\ge0$,
--   $$\rho_{D-1}(\sigma_{D,m})\le a_D(m)\le\Big(\frac32-\frac1{2D^2}\Big)\Big(1-\frac1{D^2}\Big)^m\le\frac32e^{-m/D^2}.$$
--   2. If $m\ge D^2$, then $a_D(m)\le e^{-m/(2D^2)}$.
--   3. Disjoint cores on blocks of sizes $m_i\ge D^2$ with $n=\sum_im_i$ satisfy
--   $$\rho_{D-1}\Big(\bigoplus_i\sigma_{D,m_i}\Big)\le\prod_ia_D(m_i)\le e^{-n/(2D^2)}.$$
--   4. If $D$ is the first power of two with $D>d\ge1$, this gives $\rho_d\big(\bigoplus_i\sigma_{D,m_i}\big)\le e^{-n/(8d^2)}$.
--
--   Every competing polynomial of degree at most $d$ (resp. $D-1$) is allowed, even if its monomials cross all the core blocks.
--
--   Differences from the source:
--   - encoding: disjoint blocks → the variable set `Σ i : Fin k, Fin (ms i)` (`xorBlocks`), any number $k$ of blocks; reason: relabelling
--   - encoding: "the first power of two $D>d$" → `IsDyadic D`, `d < D`, and `D ≤ D'` for every dyadic `D' > d`; reason: definition of the least such power
--   - encoding: $e^{x}$ → `Real.exp`; reason: notation
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 28 (PDF 30), Corollary 3.7

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Corollary 3.7** (Unrestricted rational elementary-core bound; Xin Li, *More on Correlation
Bounds for Polynomials*, p. 28, PDF 30). For dyadic `D ≥ 2`:
(1) for all `m ≥ 0`, `ρ_{D−1}(σ_{D,m}) ≤ a_D(m) ≤ (3/2 − 1/(2D²))(1 − 1/D²)^m ≤ (3/2) e^{−m/D²}`;
(2) if `m ≥ D²`, then `a_D(m) ≤ e^{−m/(2D²)}`;
(3) disjoint cores on blocks `m_i ≥ D²` with `n = ∑_i m_i` satisfy
`ρ_{D−1}(⨁_i σ_{D,m_i}) ≤ ∏_i a_D(m_i) ≤ e^{−n/(2D²)}`;
(4) if `D` is the first power of two with `D > d ≥ 1`, then `ρ_d(⨁_i σ_{D,m_i}) ≤ e^{−n/(8d²)}`.
Every competing polynomial of degree at most `d` (resp. `D − 1`) is allowed, cross-block monomials
included. -/
theorem corollary_3_7 (D : ℕ) (hD : IsDyadic D) (hD2 : 2 ≤ D) :
    (∀ m : ℕ,
      rho (D - 1) (evalFn (sigma D m)) ≤ aD D m ∧
      aD D m ≤ (3 / 2 - 1 / (2 * (D : ℝ) ^ 2)) * (1 - 1 / (D : ℝ) ^ 2) ^ m ∧
      (3 / 2 - 1 / (2 * (D : ℝ) ^ 2)) * (1 - 1 / (D : ℝ) ^ 2) ^ m ≤
        3 / 2 * Real.exp (-(m : ℝ) / (D : ℝ) ^ 2)) ∧
    (∀ m : ℕ, D ^ 2 ≤ m → aD D m ≤ Real.exp (-(m : ℝ) / (2 * (D : ℝ) ^ 2))) ∧
    (∀ (k : ℕ) (ms : Fin k → ℕ), (∀ i, D ^ 2 ≤ ms i) →
      rho (D - 1) (xorBlocks fun i => evalFn (sigma D (ms i))) ≤ ∏ i, aD D (ms i) ∧
      ∏ i, aD D (ms i) ≤ Real.exp (-((∑ i, ms i : ℕ) : ℝ) / (2 * (D : ℝ) ^ 2))) ∧
    (∀ d : ℕ, 1 ≤ d → d < D → (∀ D' : ℕ, IsDyadic D' → d < D' → D ≤ D') →
      ∀ (k : ℕ) (ms : Fin k → ℕ), (∀ i, D ^ 2 ≤ ms i) →
        rho d (xorBlocks fun i => evalFn (sigma D (ms i))) ≤
          Real.exp (-((∑ i, ms i : ℕ) : ℝ) / (8 * (d : ℝ) ^ 2))) := by sorry

end CorrBoundsPoly.ExactDegree
