-- Prove2me | Theorems.Thm_BilateralOptRegret_theorem_8_1
-- name    : BilateralOptRegret.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:10.543237+00:00
-- url     : https://prove2.me/theorems/4199f117-75c3-44b8-b6b6-6da1c1763f3b
-- title:
--   Theorem 8.1 (corrected: $K\ge3$) — row-wise refinement
-- statement:
--   There is an absolute constant $C_0>0$ with the following property. Let $K=2^n+1$, $n\ge1$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, $\varepsilon_{i+1}=\varepsilon/8$, and let $(G,\hat F)$ satisfy (15) and (16). With probability at least $1-\delta$, Algorithm 3 returns $G_{\mathrm{tar}}$ and estimates with
--   $$\max_{x\in G_{\mathrm{tar}}}|\hat F_{\mathrm{new}}(x)-F(x)|\le\varepsilon_{i+1}.$$
--   On the same event, its sample complexity is at most $C_0\log(24K^3/\delta)[K\ell_K^2\varepsilon_{i+1}^{-2}+\ell_K^6\varepsilon_{i+1}^{-3}]$, every queried point belongs to $G_{\mathrm{qry}}$ and has gap at most $102\varepsilon\ell_K$, and the regret of the procedure relative to the best grid action is at most
--   $$C_0\,\varepsilon\,\ell_K\log\frac{24K^3}{\delta}\Big[K\ell_K^2\varepsilon_{i+1}^{-2}+\ell_K^6\varepsilon_{i+1}^{-3}\Big].$$
--
--   Differences from the source:
--   - correction: all $K\ge2$ with $K-1$ a power of two → $n\ge1$, i.e. $K\ge3$; reason: false at $K=2$, where $\mathcal I^\star=\emptyset$: take $L=\delta_{(1,0)}$, $G=\mathcal X_2$, $\hat F=F$; (15), (16) hold, $x_{0,0},x_{1,0}\in G_{tar}$ since $r$ is $0$ at both and $\mathrm{OPT}=0$, yet the reconstruction gives $\hat D_0(1,0)=0$ while $D_0(1,0)=1$
--   - encoding: "the regret incurred by the procedure relative to the best grid action" → the sum of $\mathrm{gap}$ over the list of its queries; reason: this is the meaning given in the proof, p.41
--   - encoding: $O(\cdot)$ → $\exists C_0>0$ before all quantifiers; reason: the page's constants are absolute
--   - encoding: $0<\varepsilon_i\le 1$ (§8.3, p.41), $\delta\in(0,1)$ (Definition 4.1) → the same bounds as hypotheses; reason: standing assumptions of the page; the counts absorb the ceilings of $n_A,n_B$ using them
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Theorem 8.1, p.40

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Maps
import Definitions.Def_BilateralOptRegret_Refine

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Theorem 8.1** (corrected: `K ≥ 3`), Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.40: row-wise refinement.

Under (15), (16), with `ε_{i+1} = ε/8`: with probability at least `1 − δ`, Algorithm 3 returns `G_tar` and estimates with `max_{x ∈ G_tar} |F̂_new(x) − F(x)| ≤ ε_{i+1}`; on the same event it uses
`O(log(24K³/δ) [K ℓ_K² ε_{i+1}⁻² + ℓ_K⁶ ε_{i+1}⁻³])` observations, (29), every queried point is in `G_qry` with gap at most `102 ε ℓ_K`, and the regret of the procedure relative to the best grid action is
`O(ε ℓ_K log(24K³/δ) [K ℓ_K² ε_{i+1}⁻² + ℓ_K⁶ ε_{i+1}⁻³])`.

**Formalization Note.** The regret of the procedure is the sum of `gap` over the list of its queries. The returned set is asserted to be `G_tar`. -/
theorem theorem_8_1 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (sel : Finset (Idx n) → Idx n) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε δ : ℝ)
        (L : Measure (ℝ × ℝ)),
      1 ≤ n → IsSel sel → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 → IsValLaw L →
      Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat →
      ENNReal.ofReal (1 - δ) ≤
        succProb L (Kof n) (refineAlg sel G Fhat ε δ) (fun o =>
          o.1.1 = gTar G Fhat ε ∧
          (∀ q ∈ gTar G Fhat ε, |o.1.2 q - F L (pt (Kof n) q)| ≤ ε / 8) ∧
          (o.2.length : ℝ) ≤ C₀ * Real.log (24 * (Kof n : ℝ) ^ 3 / δ) * ((Kof n : ℝ) * (ell n : ℝ) ^ 2 * (ε / 8) ^ (-2 : ℤ) + (ell n : ℝ) ^ 6 * (ε / 8) ^ (-3 : ℤ)) ∧
          (∀ q ∈ o.2, q ∈ gQry G Fhat ε ∧ gap L (Kof n) q ≤ 102 * ε * (ell n : ℝ)) ∧
          (o.2.map (gap L (Kof n))).sum ≤ C₀ * (ε * (ell n : ℝ)) * Real.log (24 * (Kof n : ℝ) ^ 3 / δ) * ((Kof n : ℝ) * (ell n : ℝ) ^ 2 * (ε / 8) ^ (-2 : ℤ) + (ell n : ℝ) ^ 6 * (ε / 8) ^ (-3 : ℤ))) := by sorry

end BilateralOptRegret
