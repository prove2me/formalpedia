-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_7_1
-- name    : BilateralOptRegret.lemma_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:45.064385+00:00
-- url     : https://prove2.me/theorems/92f3c764-87d9-4e60-87b3-a40344f3263d
-- title:
--   Lemma 7.1 — threshold separation $22$ / $102$ / $98$ / $16$
-- statement:
--   Let $\varepsilon>0$, and let $(G,\hat F)$ satisfy (15) and (16): every $x\in\mathcal X_K$ with $\mathrm{gap}(x)\le128\varepsilon\ell_K$ is in $G$, and $\max_{x\in G}|\hat F(x)-F(x)|\le\varepsilon$. Then, with the sets (17),
--   $$\mathrm{gap}(x)\le22\varepsilon\ell_K\ \ \forall x\in G_{\mathrm{tar}},\quad\mathrm{gap}(x)\le102\varepsilon\ell_K\ \ \forall x\in G_{\mathrm{qry}},\quad\mathrm{gap}(x)>98\varepsilon\ell_K\ \ \forall x\notin G_{\mathrm{qry}},$$
--   and every point with $\mathrm{gap}(x)\le16\varepsilon\ell_K=128\varepsilon_{i+1}\ell_K$ is in $G_{\mathrm{tar}}$, where $\varepsilon_{i+1}=\varepsilon/8$.
--
--   This is the separation that makes replacing a representative worthwhile.
--
--   Differences from the source:
--   - generalization: $0<\varepsilon_i\le1$ (§8.3, p.41) → $0<\varepsilon$ only; reason: the proof does not use $\varepsilon_i\le 1$, so the page's range is a special case
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 7.1, p.27

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 7.1**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.27: threshold separation.

Under (15) and (16): `gap(x) ≤ 22 ε ℓ_K` on `G_tar`, `gap(x) ≤ 102 ε ℓ_K` on `G_qry`, `gap(x) > 98 ε ℓ_K` off `G_qry`, and every point with
`gap(x) ≤ 16 ε ℓ_K = 128 ε_{i+1} ℓ_K` is in `G_tar`.

**Formalization Note.** `ε` is the phase precision `ε_i` (`0 < ε_i`, §8.3, p.41). (15) and (16) are `Invariant L K (128 ℓ_K) ε G F̂`. "`x ∉ G_qry`" ranges over all of `X_K`,
including `x ∉ G`. -/
theorem lemma_7_1 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (G : Finset (Act n))
    (Fhat : Act n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hinv : Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat) :
    (∀ q ∈ gTar G Fhat ε, gap L (Kof n) q ≤ 22 * ε * (ell n : ℝ)) ∧
    (∀ q ∈ gQry G Fhat ε, gap L (Kof n) q ≤ 102 * ε * (ell n : ℝ)) ∧
    (∀ q, q ∉ gQry G Fhat ε → 98 * ε * (ell n : ℝ) < gap L (Kof n) q) ∧
    ∀ q, gap L (Kof n) q ≤ 16 * ε * (ell n : ℝ) → q ∈ gTar G Fhat ε := by sorry

end BilateralOptRegret
