-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_8_2
-- name    : BilateralOptRegret.lemma_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:33.164702+00:00
-- url     : https://prove2.me/theorems/ac6c9a5d-b827-4636-a8e7-ab61716107df
-- title:
--   Lemma 8.2 — preservation of the refinement invariant
-- statement:
--   Let $(G,\hat F)$ satisfy (15) and (16) at precision $\varepsilon>0$, let $\varepsilon_{i+1}=\varepsilon/8$, and let $\hat F_{\mathrm{new}}$ satisfy $\max_{x\in G_{\mathrm{tar}}}|\hat F_{\mathrm{new}}(x)-F(x)|\le\varepsilon_{i+1}$. Then
--   $$\{x\in\mathcal X_K:\mathrm{gap}(x)\le128\varepsilon_{i+1}\ell_K\}\subseteq G_{\mathrm{tar}},\qquad\max_{x\in G_{\mathrm{tar}}}|\hat F_{\mathrm{new}}(x)-F(x)|\le\varepsilon_{i+1}.$$
--   The output of a phase is therefore a valid input of the next one.
--
--   Differences from the source:
--   - generalization: $0<\varepsilon_i\le1$ (§8.3, p.41) → $0<\varepsilon$ only; reason: the page's range is a special case
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 8.2, p.41

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Maps

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 8.2**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.41: preservation of the refinement invariant.

If the input satisfies (15), (16) and `max_{x ∈ G_tar} |F̂_new(x) − F(x)| ≤ ε_{i+1}`, then `{x ∈ X_K : gap(x) ≤ 128 ε_{i+1} ℓ_K} ⊆ G_tar` and `max_{x ∈ G_tar} |F̂_new(x) − F(x)| ≤ ε_{i+1}`, (30).

**Formalization Note.** (30) is `Invariant L K (128 ℓ_K) (ε/8) G_tar F̂_new`. `F̂_new` is any function with the assumed precision. -/
theorem lemma_8_2 (n : ℕ) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) (G : Finset (Act n))
    (Fhat Fnew : Act n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hinv : Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat)
    (hnew : ∀ q ∈ gTar G Fhat ε, |Fnew q - F L (pt (Kof n) q)| ≤ ε / 8) :
    Invariant L (Kof n) (128 * (ell n : ℝ)) (ε / 8) (gTar G Fhat ε) Fnew := by sorry

end BilateralOptRegret
