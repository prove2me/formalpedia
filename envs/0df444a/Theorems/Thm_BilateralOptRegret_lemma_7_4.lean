-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_4
-- name    : BilateralOptRegret.lemma_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:14.689647+00:00
-- url     : https://prove2.me/theorems/fa7b3118-0319-434c-a70d-a0108f0ee237
-- title:
--   Lemma 7.4 — each representative replacement gains more than $76\varepsilon\ell_K$
-- statement:
--   Let $(G,\hat F)$ satisfy (15) and (16) at precision $\varepsilon>0$, and let $v_{-1}=\mathrm{id},v_0,\dots,v_{K-1}$ be the maps constructed by Algorithm 2 on the sets (17). For every column $i$ and row $j$ with $v_j(i)\ne v_{j-1}(i)$,
--   $$r(x_{v_j(i),j})-r(x_{v_{j-1}(i),j})>76\,\varepsilon\,\ell_K.$$
--   Each replacement therefore yields a definite profit increase, which the potential converts into a bound on their number.
--
--   Differences from the source:
--   - generalization: $0<\varepsilon_i\le1$ (§8.3, p.41) → $0<\varepsilon$ only; reason: the page's range is a special case
--   - encoding: $\varepsilon_i$, with $i$ also the column → $\varepsilon$ for the phase precision and $i$ for the column; reason: the clash of letters is on the page; p.27 shows $\varepsilon_i$ is the phase precision
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.4, p.30

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.4**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.30: gain from a representative replacement.

Under (15), (16), with `v_j` from Algorithm 2 on the sets (17): for every column `i` and row `j` with `v_j(i) ≠ v_{j−1}(i)`, `r(x_{v_j(i),j}) − r(x_{v_{j−1}(i),j}) > 76 ε ℓ_K`.

**Formalization Note.** `ε` is the phase precision (the page's `ε_i`) and `i` the column. `v_j = repAfter … (j + 1)` and `v_{j−1} = repAfter … j`, so `j = 0` compares with `v_{−1} = id` (p.30). -/
theorem lemma_7_4 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (sel : Finset (Idx n) → Idx n)
    (hsel : IsSel sel) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hinv : Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat) (i j : Idx n)
    (hne : repAfter sel (gTar G Fhat ε) (gQry G Fhat ε) (j.val + 1) i ≠ repAfter sel (gTar G Fhat ε) (gQry G Fhat ε) j.val i) :
    76 * ε * (ell n : ℝ) <
      r L (pt (Kof n) (repAfter sel (gTar G Fhat ε) (gQry G Fhat ε) (j.val + 1) i, j)) -
        r L (pt (Kof n) (repAfter sel (gTar G Fhat ε) (gQry G Fhat ε) j.val i, j)) := by sorry

end BilateralOptRegret
