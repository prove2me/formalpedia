-- Prove2me | Theorems.Thm_BilateralOptRegret_theorem_7_9
-- name    : BilateralOptRegret.theorem_7_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:43:08.103498+00:00
-- url     : https://prove2.me/theorems/31d4fec1-1d89-4964-b4ea-75befbf014ac
-- title:
--   Theorem 7.9 — cumulative probability mass $V\le(2\ell_K-1)(\ell_K-1)$
-- statement:
--   Let $\mathcal P$ be the collection of blocks induced by the maps of Algorithm 2 and, for each block $\rho$, let $R_\rho$ be its region. Then, for every law $L$ on $[0,1]^2$,
--   $$V=\sum_{\rho\in\mathcal P}\mathbb P(X\in R_\rho)\le(2\ell_K-1)(\ell_K-1)=O(\ell_K^2).$$
--   The regions may overlap, but each point is counted only polylogarithmically often. This establishes the paper's Requirement 1.4.
--
--   **Formalization Note** As on p.24, the sum ranges over the blocks requiring a BinS call.
--
--   Differences from the source:
--   - generalization: the sets of (17) → arbitrary sets $G_{tar},G_{qry}$; reason: the proof uses only the locality of the maps; the sets of (17) are an instance
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Theorem 7.9, p.36

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Maps
import Definitions.Def_BilateralOptRegret_Blocks

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Theorem 7.9**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.36: cumulative probability mass.

For the blocks induced by the mappings of Algorithm 2, `V = ∑_ρ P(X ∈ R_ρ) ≤ (2ℓ_K − 1)(ℓ_K − 1)`, the sum over the blocks requiring a BinS call (p.24).

**Formalization Note.** Neither (15), (16) nor `G_tar ⊆ G_qry` is needed. -/
theorem theorem_7_9 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (sel : Finset (Idx n) → Idx n)
    (hsel : IsSel sel) (Gtar Gqry : Finset (Act n)) :
    massV L (fun j => repAfter sel Gtar Gqry (j + 1)) Gqry ≤
      (2 * (ell n : ℝ) - 1) * ((ell n : ℝ) - 1) := by sorry

end BilateralOptRegret
