-- Prove2me | Theorems.Thm_BilateralOptRegret_proposition_7_10
-- name    : BilateralOptRegret.proposition_7_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:19.180214+00:00
-- url     : https://prove2.me/theorems/fdee5183-6c2b-46b6-89cf-5b436146b936
-- title:
--   Proposition 7.10 (corrected: $K\ge3$) — row-wise relative learning
-- statement:
--   There is an absolute constant $C_0>0$ with the following property. Let $K=2^n+1$, $n\ge1$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, $\varepsilon_{i+1}=\varepsilon/8$, and let $(G,\hat F)$ satisfy (15) and (16). With probability at least $1-\delta/2$, the relative-learning procedure of Algorithm 3 returns estimates such that, for every pair $x_{a,j},x_{b,j}\in G_{\mathrm{tar}}$ on one row,
--   $$|\hat D_j(a,b)-D_j(a,b)|\le\frac{\varepsilon_{i+1}}{4},$$
--   and on the same event the number of observations is at most
--   $$C_0\log\frac{24K^3}{\delta}\Big[K\ell_K^2\varepsilon_{i+1}^{-2}+\ell_K^6\varepsilon_{i+1}^{-3}\Big],$$
--   every query belonging to $G_{\mathrm{qry}}$ and having suboptimality gap at most $102\varepsilon\ell_K$.
--
--   This is the core learning guarantee: the $\varepsilon^{-3}$ term has no factor of $K$.
--
--   Differences from the source:
--   - correction: all $K\ge2$ with $K-1$ a power of two → $n\ge1$, i.e. $K\ge3$; reason: false at $K=2$, where $\mathcal I^\star=\emptyset$: take $L=\delta_{(1,0)}$, $G=\mathcal X_2$, $\hat F=F$; (15), (16) hold, $x_{0,0},x_{1,0}\in G_{tar}$ since $r$ is $0$ at both and $\mathrm{OPT}=0$, yet the reconstruction gives $\hat D_0(1,0)=0$ while $D_0(1,0)=1$
--   - generalization: "there exists a relative-learning procedure" → the explicit procedure `relLearn`, lines 2–14 of Algorithm 3; reason: it witnesses the existential, and it is the procedure the page describes before the statement
--   - encoding: $O(\cdot)$ → $\exists C_0>0$ before all quantifiers; reason: the page's constants are absolute
--   - encoding: $0<\varepsilon_i\le 1$ (§8.3, p.41), $\delta\in(0,1)$ (Definition 4.1) → the same bounds as hypotheses; reason: standing assumptions of the page; the counts absorb the ceilings of $n_A,n_B$ using them
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Proposition 7.10, p.37

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Oracle
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Maps
import Definitions.Def_BilateralOptRegret_Blocks
import Definitions.Def_BilateralOptRegret_Refine

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Proposition 7.10** (corrected: `K ≥ 3`), Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.37: row-wise relative learning.

Under (15), (16), with `ε_{i+1} = ε/8`: with probability at least `1 − δ/2`, the procedure returns estimates with `|D̂_j(a, b) − D_j(a, b)| ≤ ε_{i+1}/4` for every pair `x_{a,j}, x_{b,j} ∈ G_tar` on a row; on the same event it uses
`O(log(24K³/δ) [K ℓ_K² ε_{i+1}⁻² + ℓ_K⁶ ε_{i+1}⁻³])` observations, (27), with an absolute constant, every query in `G_qry` with gap at most `102 ε ℓ_K`.

**Formalization Note.** "There exists a relative-learning procedure" is the explicit `relLearn`, lines 2–14 of Algorithm 3, as described on p.37, which implies the existence. `D̂` is computed from its table by (19). `0 < ε ≤ 1` is standing (§8.3, p.41), `δ ∈ (0, 1)` as in Definition 4.1. `n ≥ 1` because the printed statement fails at `K = 2`, where `I⋆ = ∅` makes every estimate `0`. -/
theorem proposition_7_10 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (sel : Finset (Idx n) → Idx n) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε δ : ℝ)
        (L : Measure (ℝ × ℝ)),
      1 ≤ n → IsSel sel → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 → IsValLaw L →
      Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat →
      ENNReal.ofReal (1 - δ / 2) ≤
        succProb L (Kof n) (relLearn sel G Fhat ε δ) (fun o =>
          (∀ (j a b : Idx n), (a, j) ∈ gTar G Fhat ε → (b, j) ∈ gTar G Fhat ε →
            |Dhat o.1 j a b - rowDiff L (Kof n) j a b| ≤ (ε / 8) / 4) ∧
          (o.2.length : ℝ) ≤ C₀ * Real.log (24 * (Kof n : ℝ) ^ 3 / δ) * ((Kof n : ℝ) * (ell n : ℝ) ^ 2 * (ε / 8) ^ (-2 : ℤ) + (ell n : ℝ) ^ 6 * (ε / 8) ^ (-3 : ℤ)) ∧
          ∀ q ∈ o.2, q ∈ gQry G Fhat ε ∧ gap L (Kof n) q ≤ 102 * ε * (ell n : ℝ)) := by sorry

end BilateralOptRegret
