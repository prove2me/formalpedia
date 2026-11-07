-- Prove2me | Theorems.Thm_BilateralOptRegret_eq_25
-- name    : BilateralOptRegret.eq_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:04.802412+00:00
-- url     : https://prove2.me/theorems/3b7a41f0-bb75-400a-aa54-92d1cefdde46
-- title:
--   Display (25) — number of fixed-endpoint blocks
-- statement:
--   Let $(G,\hat F)$ satisfy (15) and (16) at precision $\varepsilon>0$, with $v_j$ from Algorithm 2 on the sets (17). Then
--   $$C\le(2\ell_K-1)\sum_{j=1}^{K-1}\sum_{i=0}^{K-1}\mathbb 1\{v_j(i)\ne v_{j-1}(i)\},\qquad|\mathcal P|\le3K+C,$$
--   and hence
--   $$|\mathcal P|\le3K+(2\ell_K-1)\frac{6}{76\,\varepsilon},$$
--   which gives $|\mathcal P|=O(K+\ell_K/\varepsilon)$. This establishes the paper's Requirement 1.3.
--
--   Differences from the source:
--   - generalization: $|\mathcal P|\le 3K+C=O(K+\ell_K/\varepsilon_i)$ → the explicit bound $3K+(2\ell_K-1)\cdot6/(76\varepsilon)$; reason: it implies the $O(\cdot)$, with explicit constants from the same page
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Display (25) and the bound on $C$, p.34

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Maps
import Definitions.Def_BilateralOptRegret_Blocks
import Definitions.Def_BilateralOptRegret_Refine

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Display (25)**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.34: number of fixed-endpoint blocks.

Under (15), (16), with `v_j` from Algorithm 2 on the sets (17): `C ≤ (2ℓ_K − 1) ∑_{j=1}^{K−1} ∑_i 1{v_j(i) ≠ v_{j−1}(i)}`, `|P| ≤ 3K + C`, and so `|P| ≤ 3K + (2ℓ_K − 1) · 6/(76 ε)`.

**Formalization Note.** The explicit last bound gives the printed `O(K + ℓ_K/ε)`. -/
theorem eq_25 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (sel : Finset (Idx n) → Idx n)
    (hsel : IsSel sel) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hinv : Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat) :
    changeCount (mapsOf sel G Fhat ε) ≤ (2 * ell n - 1) * replacements (repAfter sel (gTar G Fhat ε) (gQry G Fhat ε)) ∧
    (blocks (mapsOf sel G Fhat ε)).card ≤ 3 * Kof n + changeCount (mapsOf sel G Fhat ε) ∧
    ((blocks (mapsOf sel G Fhat ε)).card : ℝ) ≤
      3 * (Kof n : ℝ) + (2 * (ell n : ℝ) - 1) * (6 / (76 * ε)) := by sorry

end BilateralOptRegret
