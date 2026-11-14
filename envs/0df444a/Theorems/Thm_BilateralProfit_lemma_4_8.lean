-- Prove2me | Theorems.Thm_BilateralProfit_lemma_4_8
-- name    : BilateralProfit.lemma_4_8
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T02:19:54.324639+00:00
-- url     : https://prove2.me/theorems/210b0f06-aa0a-474e-97bf-6fbd09916493
-- title:
--   Lemma 4.8 — the localized estimation routine, with Remark 4.12 (corrected: $K\ge2$)
-- statement:
--   There is a constant $C$ such that for every $K\ge2$, every distribution $\rho$ on $G_K\times\mathcal A$ and every precision $\varepsilon\in(0,1]$ there is a routine, depending only on $K$, $\rho$ and $\varepsilon$, such that:
--
--   1. it makes at most $C\log^3K\,\big(K/\varepsilon^2+\log^3K/\varepsilon^3\big)$ pricing queries on every run;
--   2. every action $a\in\mathcal A$ it queries satisfies $\Delta_\rho(a^\star,a)\le2\varepsilon$;
--   3. for every unknown valuation law $P$ on $[0,1]^2$, every interval $[c,c+2]$, and every family of observation laws carried by $[c,c+2]$ with mean $P(a)$ at each action $a$ (independent draws at each query), with probability at least $9/10$ its estimates $\hat\mu$ satisfy
--   $$|\hat\mu(a)-\mathbb E_P[\mathrm{Profit}(\tilde V,a)]|\le\varepsilon/4\quad\text{for all }a\in\mathcal A\text{ with }\Delta_\rho(a^\star,a)\le\varepsilon .$$
--
--   The trade bit is the observation with $c=0$; Remark 4.12 extends the routine to any observation with the same mean in a fixed range of bounded length, which Lemma 4.5's proof uses with the rescaled bit $2Z-1/2\in\{-1/2,3/2\}$.
--
--   **Formalization Note** The routine is a deterministic adaptive query tree over $\mathcal A$; its output is a vector of estimates. $\mathbb E_P[\mathrm{Profit}(\tilde V,(p,q))]=(q-p)P(p,q)$. Logarithms are natural.
--
--   Differences from the source:
--   - correction: every $K$ → $K\ge2$; reason: at $K=1$ the bound is $0$ queries, so the output is fixed; for $\rho$ concentrated on valuation $(1,1)$, $\varepsilon=1$ and the target $a=(0,1)$ (gap $0$), the point masses at $(0,1)$ and $(1,1)$ give $\mathbb E_P[\mathrm{Profit}]=1$ and $0$, and no fixed estimate is within $1/4$ of both; every use in the paper has $K\ge2$
--   - generalization: feedback the random trade bit (Lemma 4.8), or "a generic random variable with the same average and taking values in a fixed range of bounded length" (Remark 4.12) → observations with mean $P(a)$ carried by $[c,c+2]$, with $c$ quantified after the routine; reason: the trade bit is the case $c=0$ and the bit of Lemma 4.5's proof the case $c=-1/2$; Remark 4.12 states the routine applies with the same guarantees
--   - reading: "there exists a routine"; "for some constant $C$" → a deterministic adaptive routine chosen from $(K,\rho,\varepsilon)$ only, with the query bound on every run; $C$ chosen before $K,\rho,\varepsilon$; reason: the routine of the proof is deterministic and capped; Lemma 4.5 and Theorem 4.2 use one $C$ for all $K$
--   - encoding: probability at least $9/10$; $a^\star$ optimal according to $\rho$ → $\mathrm{ofReal}(9/10)\le$ the routine's success probability; $\Delta_\rho(a^\star,\cdot)$ through the maximum value `optVal`; reason: same instances; the gap does not depend on the maximizer
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 4.8, p.24 (PDF 26); Remark 4.12, p.28 (PDF 30)

import Mathlib
import Definitions.Def_BilateralProfit_Analysis
import Definitions.Def_BilateralProfit_QueryRoutine

namespace BilateralProfit

open MeasureTheory

/-- **Lemma 4.8** with **Remark 4.12**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.24 (PDF 26) and p.28 (PDF 30); corrected: `K ≥ 2`.

There is a constant `C` such that for every `K ≥ 2`, every distribution `ρ` on `G_K × 𝒜` and every
precision `ε ∈ (0, 1]` there is a routine, depending only on `K, ρ, ε`, that
1. makes at most `C log³K (K/ε² + log³K/ε³)` pricing queries on every run,
2. queries only actions `a ∈ 𝒜` with `Δ_ρ(a⋆, a) ≤ 2ε`, and
3. for every unknown valuation law `P` on `[0,1]²`, when each query at `a` returns an independent
   observation with mean `P(a)` (the trade probability) and values in a fixed interval of length
   `2` (Remark 4.12; the trade bit is the case `[0, 2]`), estimates `E_P[Profit(Ṽ, a)]` to
   precision `ε/4` simultaneously for all `a ∈ 𝒜` with `Δ_ρ(a⋆, a) ≤ ε`, with probability at
   least `9/10`.

**Formalization Note.** The routine is a `QTree` over actions; its output is a vector of
estimates. Observations at the same action are i.i.d. with law `obs a`. `C` is chosen before
`K, ρ, ε`; the routine before `P`, the interval `[c, c + 2]` and the observation laws.
`E_P[Profit(Ṽ, a)] = (q − p) P(a)` (`muP`). `log` is natural. -/
theorem lemma_4_8 :
    ∃ C : ℝ, ∀ K : ℕ, 2 ≤ K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        ∃ (R : QTree (Act K) (Act K → ℝ)) (N : ℕ),
          (N : ℝ) ≤ C * Real.log K ^ 3 * ((K : ℝ) / ε ^ 2 + Real.log K ^ 3 / ε ^ 3) ∧
          R.QueriesAtMost N ∧ R.AllQueries (fun a => gapStar ρ a ≤ 2 * ε) ∧
          ∀ μ : Measure (ℝ × ℝ), IsValLaw μ →
            ∀ (c : ℝ) (obs : Act K → Measure ℝ), (∀ a, IsProbabilityMeasure (obs a)) →
              (∀ a, obs a (Set.Icc c (c + 2))ᶜ = 0) →
              (∀ a, ∫ r, r ∂(obs a) = Ptrade μ (pt K a.1)) →
              ENNReal.ofReal (9 / 10) ≤
                R.prob (fun a _ => obs a)
                  (fun est => ∀ a, gapStar ρ a ≤ ε → |est a - muP μ (pt K a.1)| ≤ ε / 4)
                  (fun _ => 0) := by sorry

end BilateralProfit
