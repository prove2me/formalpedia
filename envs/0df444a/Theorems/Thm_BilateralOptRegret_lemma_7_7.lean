-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_7
-- name    : BilateralOptRegret.lemma_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:01.077349+00:00
-- url     : https://prove2.me/theorems/db561f37-4926-400c-b44b-fcb590f5808d
-- title:
--   Lemma 7.7 — at most $6/(76\varepsilon)$ representative replacements
-- statement:
--   Let $(G,\hat F)$ satisfy (15) and (16) at precision $\varepsilon>0$, and let $v_j$ be the maps of Algorithm 2 on the sets (17). Then
--   $$\sum_{j=1}^{K-1}\sum_{i=0}^{K-1}\mathbb 1\{v_j(i)\ne v_{j-1}(i)\}\le\frac{6}{76\,\varepsilon}.$$
--   So the number of replacements depends on the precision and not on the grid size.
--
--   Differences from the source:
--   - encoding: "By construction" → (15), (16) and (17) as hypotheses; reason: the page's proof goes through Lemma 7.4, whose hypotheses these are
--   - generalization: $0<\varepsilon_i\le1$ (§8.3, p.41) → $0<\varepsilon$ only; reason: the page's range is a special case
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.7, p.34

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.7**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.34: number of representative replacements.

Under (15), (16), with `v_j` from Algorithm 2 on the sets (17): `∑_{j=1}^{K−1} ∑_{i=0}^{K−1} 1{v_j(i) ≠ v_{j−1}(i)} ≤ 6/(76 ε)`.

**Formalization Note.** `ε` is the phase precision. "By construction" on the page refers to Lemma 7.4, whose hypotheses are taken here. -/
theorem lemma_7_7 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (sel : Finset (Idx n) → Idx n)
    (hsel : IsSel sel) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hinv : Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat) :
    (replacements (repAfter sel (gTar G Fhat ε) (gQry G Fhat ε)) : ℝ) ≤ 6 / (76 * ε) := by sorry

end BilateralOptRegret
