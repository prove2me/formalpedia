-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_5
-- name    : BilateralOptRegret.lemma_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:12.538874+00:00
-- url     : https://prove2.me/theorems/aeace787-2edf-409c-ab09-ba6e4117c26b
-- title:
--   Lemma 7.5 — potential range and row variation
-- statement:
--   Let $L$ be a law on $[0,1]^2$. For every admissible map $v$ and every row $j$,
--   $$-2\ell_K\le\Phi(v,j)\le\ell_K.$$
--   Moreover, for every sequence of admissible maps $v_0,\dots,v_{K-1}$,
--   $$\sum_{j=0}^{K-2}\big|\Phi(v_j,j+1)-\Phi(v_j,j)\big|\le3\ell_K.$$
--   These bounds control the telescoping of the potential across rows, and hold for every law, including atoms.
--
--   Differences from the source:
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.5, p.32

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.5**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.32: potential range and row variation.

For every admissible `v` and row `j`, `−2 ℓ_K ≤ Φ(v, j) ≤ ℓ_K`. For every sequence of admissible maps `v_0, …, v_{K−1}`, `∑_{j=0}^{K−2} |Φ(v_j, j + 1) − Φ(v_j, j)| ≤ 3 ℓ_K`, (23).

**Formalization Note.** Admissible means `v(i) ∈ I_i` for internal `i` (p.30). The sequence is `vs j`, `j ∈ {0, …, K − 1}`; the sum runs over the row pairs. Rows are `Fin.ofNat` of naturals. -/
theorem lemma_7_5 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) :
    (∀ v : Idx n → Idx n, Admissible v → ∀ j : Idx n,
      -2 * (ell n : ℝ) ≤ potential L v j ∧ potential L v j ≤ (ell n : ℝ)) ∧
    ∀ vs : ℕ → Idx n → Idx n, (∀ j, j < Kof n → Admissible (vs j)) →
      ∑ j ∈ Finset.range (2 ^ n),
        |potential L (vs j) (Fin.ofNat (Kof n) (j + 1)) - potential L (vs j) (Fin.ofNat (Kof n) j)|
        ≤ 3 * (ell n : ℝ) := by sorry

end BilateralOptRegret
