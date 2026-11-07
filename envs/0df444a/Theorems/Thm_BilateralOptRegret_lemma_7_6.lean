-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_6
-- name    : BilateralOptRegret.lemma_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:43.682958+00:00
-- url     : https://prove2.me/theorems/62d88fbd-61d7-4ba9-a0e8-858e0baefc85
-- title:
--   Lemma 7.6 — cumulative representative replacement gain $\le6\ell_K$
-- statement:
--   Let $v_{-1}=\mathrm{id}$ and let $v_0,\dots,v_{K-1}$ be the maps obtained after processing the rows in Algorithm 2. Then
--   $$\sum_{j=0}^{K-1}\big(\Phi(v_j,j)-\Phi(v_{j-1},j)\big)\le6\ell_K.$$
--   This caps the total profit gain available from replacements.
--
--   Differences from the source:
--   - generalization: the sets of (17) built from an input with (15), (16) → arbitrary sets $G_{tar},G_{qry}$; reason: the proof uses only admissibility of the maps; the sets of (17) are an instance
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.6, p.34

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.6**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.34: cumulative representative replacement gain.

With `v_{−1} = id` and `v_0, …, v_{K−1}` from Algorithm 2, `∑_{j=0}^{K−1} (Φ(v_j, j) − Φ(v_{j−1}, j)) ≤ 6 ℓ_K`, (24).

**Formalization Note.** Neither (15), (16) nor a relation between `G_tar` and `G_qry` is needed. -/
theorem lemma_7_6 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (sel : Finset (Idx n) → Idx n)
    (hsel : IsSel sel) (Gtar Gqry : Finset (Act n)) :
    ∑ j : Idx n,
      (potential L (repAfter sel Gtar Gqry (j.val + 1)) j -
        potential L (repAfter sel Gtar Gqry j.val) j) ≤ 6 * (ell n : ℝ) := by sorry

end BilateralOptRegret
