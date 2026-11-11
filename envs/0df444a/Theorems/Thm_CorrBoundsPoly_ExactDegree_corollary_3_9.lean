-- Prove2me | Theorems.Thm_CorrBoundsPoly_ExactDegree_corollary_3_9
-- name    : CorrBoundsPoly.ExactDegree.corollary_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:59:13.220056+00:00
-- url     : https://prove2.me/theorems/fbb648da-97af-4e29-836b-5044449d7342
-- title:
--   Corollary 3.9 — $\nu(\sigma_{D,m})=a_D(m)=\eta(m,D)$ and $\rho_{D-1}(\bigoplus_i\sigma_{D,m_i})=\prod_i\eta(m_i,D)$
-- statement:
--   1. For every dyadic $D\ge1$ and every $m\ge0$,
--   $$\nu(\sigma_{D,m})=a_D(m)=\eta(m,D). \tag{3.13}$$
--   2. For dyadic $D\ge2$ and any disjoint blocks of sizes $m_1,\dots,m_k$,
--   $$\rho_{D-1}\Big(\bigoplus_i\sigma_{D,m_i}\Big)=\prod_i\eta(m_i,D).$$
--
--   This is the exact degree-$(D-1)$ correlation of XORs of dyadic elementary cores, against every test of degree below $D$ including those with cross-block monomials; it supplies the attaining tests for the dyadic leaves of the exact-degree recursion.
--
--   Differences from the source:
--   - encoding: disjoint blocks → the variable set `Σ i : Fin k, Fin (ms i)` (`xorBlocks`); reason: relabelling
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), pp. 29–30 (PDF 31–32), Corollary 3.9, Eq. (3.13)

import Mathlib
import Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
import Definitions.Def_CorrBoundsPoly_ExactDegree_ElemSym

namespace CorrBoundsPoly.ExactDegree

/-- **Corollary 3.9** (Exact rank deficit and exact correlation; Xin Li, *More on Correlation Bounds
for Polynomials*, pp. 29–30, PDF 31–32). (1) For every dyadic `D ≥ 1` and every `m ≥ 0`,
`ν(σ_{D,m}) = a_D(m) = η(m, D)` (Eq. (3.13)). (2) For dyadic `D ≥ 2` and any disjoint blocks of
sizes `m_1, …, m_k`, `ρ_{D−1}(⨁_i σ_{D,m_i}) = ∏_i η(m_i, D)`. -/
theorem corollary_3_9 :
    (∀ D : ℕ, IsDyadic D → ∀ m : ℕ, nu (sigma D m) = aD D m ∧ aD D m = eta m D) ∧
    (∀ D : ℕ, IsDyadic D → 2 ≤ D → ∀ (k : ℕ) (ms : Fin k → ℕ),
      rho (D - 1) (xorBlocks fun i => evalFn (sigma D (ms i))) = ∏ i, eta (ms i) D) := by sorry

end CorrBoundsPoly.ExactDegree
