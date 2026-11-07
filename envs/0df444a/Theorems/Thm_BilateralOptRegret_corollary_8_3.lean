-- Prove2me | Theorems.Thm_BilateralOptRegret_corollary_8_3
-- name    : BilateralOptRegret.corollary_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:44:19.343608+00:00
-- url     : https://prove2.me/theorems/8042e0fa-cbdc-4062-aa38-d07e8fd5c41a
-- title:
--   Corollary 8.3 (corrected: $K\ge3$) and §9 — Algorithm 3 is a refinement oracle
-- statement:
--   There is a universal constant $c_0\ge1$ with the following property. Let $K=2^n+1$, $n\ge1$, $\varepsilon\in(0,1]$, $\delta\in(0,1)$, $\varepsilon_{i+1}=\varepsilon/8$, and let the input of Algorithm 3 satisfy (15) and (16). With probability at least $1-\delta$, its output satisfies (30), and its number of observations is at most
--   $$c_0\ell_K^6\log\Big(\frac{24K^3}{\delta}\Big)\big(\varepsilon_{i+1}^{-3}+K\varepsilon_{i+1}^{-2}\big),$$
--   every query being in $G_{\mathrm{qry}}$ with gap at most $102\varepsilon\ell_K$. Consequently (§9), Algorithm 3 is a $(c_1,c_2,A)$-refinement oracle with
--   $$c_1=128\ell_K,\qquad c_2=102\ell_K,\qquad A(K,\delta)=c_0\ell_K^6\log\frac{24K^3}{\delta}.$$
--   This supplies exactly the oracle assumed in Theorem 4.2.
--
--   Differences from the source:
--   - correction: all $K\ge2$ with $K-1$ a power of two → $n\ge1$, i.e. $K\ge3$; reason: false at $K=2$, where $\mathcal I^\star=\emptyset$: take $L=\delta_{(1,0)}$, $G=\mathcal X_2$, $\hat F=F$; (15), (16) hold, $x_{0,0},x_{1,0}\in G_{tar}$ since $r$ is $0$ at both and $\mathrm{OPT}=0$, yet the reconstruction gives $\hat D_0(1,0)=0$ while $D_0(1,0)=1$
--   - encoding: Corollary 8.3 and the sentence of §9 are separate → one statement with both conjuncts; reason: they share the constant $c_0$
--   - encoding: $0<\varepsilon_i\le 1$ (§8.3, p.41), $\delta\in(0,1)$ (Definition 4.1) → the same bounds as hypotheses; reason: standing assumptions of the page; the counts absorb the ceilings of $n_A,n_B$ using them
--   - encoding: "choose" (an arbitrary choice) → every selection rule `IsSel` on finite sets; reason: the statement holds for each way of resolving the choice by a function of the candidate set; no choice reads the law
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Corollary 8.3, p.41; §9, p.42

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

/-- **Corollary 8.3** (corrected: `K ≥ 3`), Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.41, and the oracle parameters of §9, p.42: Algorithm 3 is a refinement oracle.

There is a universal `c₀ ≥ 1` such that, under (15), (16): with probability at least `1 − δ`, the output of Algorithm 3 satisfies (30), it uses at most `c₀ ℓ_K⁶ log(24K³/δ) (ε_{i+1}⁻³ + K ε_{i+1}⁻²)` observations, (31), and every query
is in `G_qry` with gap at most `102 ε ℓ_K`. Hence Algorithm 3 is a `(128 ℓ_K, 102 ℓ_K, A)`-refinement oracle with `A(K, δ) = c₀ ℓ_K⁶ log(24K³/δ)`.

**Formalization Note.** `c₀` comes before everything. `n ≥ 1` as in Proposition 7.10; the regret goal has `n ≥ 1` for all `T ≥ 2`. -/
theorem corollary_8_3 :
    ∃ c₀ : ℝ, 1 ≤ c₀ ∧
      (∀ (n : ℕ) (sel : Finset (Idx n) → Idx n) (G : Finset (Act n)) (Fhat : Act n → ℝ) (ε δ : ℝ)
        (L : Measure (ℝ × ℝ)),
      1 ≤ n → IsSel sel → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 → IsValLaw L →
      Invariant L (Kof n) (128 * (ell n : ℝ)) ε G Fhat →
        ENNReal.ofReal (1 - δ) ≤
          succProb L (Kof n) (refineAlg sel G Fhat ε δ) (fun o =>
            Invariant L (Kof n) (128 * (ell n : ℝ)) (ε / 8) o.1.1 o.1.2 ∧
            (o.2.length : ℝ) ≤
              c₀ * (ell n : ℝ) ^ 6 * Real.log (24 * (Kof n : ℝ) ^ 3 / δ) *
                ((ε / 8) ^ (-3 : ℤ) + (Kof n : ℝ) * (ε / 8) ^ (-2 : ℤ)) ∧
            ∀ q ∈ o.2, q ∈ gQry G Fhat ε ∧ gap L (Kof n) q ≤ 102 * ε * (ell n : ℝ))) ∧
      ∀ (n : ℕ) (sel : Finset (Idx n) → Idx n), 1 ≤ n → IsSel sel →
        IsRefinementOracle n (128 * (ell n : ℝ)) (102 * (ell n : ℝ)) (paperA c₀) (refineAlg sel) := by sorry

end BilateralOptRegret
