-- Prove2me | Theorems.Thm_BilateralProfitRegular_lemma_6_6
-- name    : BilateralProfitRegular.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:39.597492+00:00
-- url     : https://prove2.me/theorems/7f19b3ef-83ba-4a73-b78f-096ce0f4ffc8
-- title:
--   Lemma 6.6 — refinement (57) holds w.p. $1-1/T$; elimination keeps $i^\star$ and gives (58)
-- statement:
--   Assume initialization triggered with the guarantees of Lemma 6.4. Let $\eta\in(0,1)$ with $\lceil1/\eta\rceil\le T$, and $\varepsilon_j=\delta2^{-j}$.
--
--   **(i) Refinement.** Let $C_1$ and $C_2$ be the constants of (50) and (55). There is $C_0$ with the following property. Fix a valid candidate $i$ and a valid calibrated parameter $\lambda$, meaning $|\log(\lambda/\lambda_i)|\le10^{-3}\sqrt{\eta/\delta}$. Let ConOpt be any $n$-query algorithm on $\mathcal K_i$ satisfying (55) with $C_2$, and let the observations satisfy (50) with $C_1$. Then in any phase $j$ started before $T$, refinement run to completion succeeds except with probability $1/T$. Refinement consists of $\lceil C_0\log(2T)\rceil$ independent copies of length $n=4^j\lceil C_0\log^4(2T)\rceil$, with selection of the smallest $\hat L$ and $\hat r=1/\max\{\hat L,1/(10\delta)\}$. Success means that it returns $y\in\mathcal K_i$ and $\hat r_i$ with
--   $$\max_{\mathcal K_i}r_\lambda-\varepsilon_j\le\hat r_i\le r_\lambda(y)+\varepsilon_j. \tag{57}$$
--
--   **(ii) Elimination.** Suppose all calibrations and refinements through a completed phase $j$ satisfy (49) and (57). Then:
--
--   - the near-optimal candidate $i^\star$ survives to phase $j+1$;
--   - every retained and updated reference $z_i^{(j+1)}$ satisfies, for the next valid calibration $\rho_i^{(j+1)}$,
--   $$\mu^\star-r_{\rho_i^{(j+1)}\lambda_{z_i^{(j+1)}}}\big(z_i^{(j+1)}\big)\le65(\eta+\varepsilon_{j+1}); \tag{58}$$
--   - the same inequality holds for $j=0$ at the roots.
--
--   Differences from the source:
--   - generalization: ConOpt (Corollary 3.1's algorithm) with the observations of Lemma 6.5(ii); "a candidate" and "$i^\star$ from Lemma 6.4" → any $n$-query algorithm on $\mathcal K_i$ satisfying (55) with $C_2$, any observation law satisfying (50) with $C_1$, any valid candidate and valid $\lambda$; in (ii) every near-optimal candidate survives; reason: the proof uses only (50), (55), Lemma 6.4's guarantees and $i^\star$'s near-optimality; the paper's ConOpt, observations and $i^\star$ are instances
--   - generalization: "Choose the run with the smallest empirical average loss" → (57) for every run attaining the smallest $\hat L$; reason: covers any tie-breaking rule
--   - encoding: "In any phase $j$ started before $T$" → $j=0$, or $4^{j-1}\lceil C_0\log^4(2T)\rceil\le T$; reason: a run of the previous phase of $\ge1$-round observations must fit in $T$ rounds, which is what the proof uses ("$n\le4T$", p.45)
--   - encoding: phases of Algorithm 8; "except with probability $1/T$" → (ii) over arbitrary sequences of active sets, references, multipliers and outputs obeying the elimination and update rules; (i) the expectation of the failure indicator over the independent copies is at most $1/T$; reason: (ii) is deterministic given its hypotheses; the copies are independent runs
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.6, pp.44–45 (PDF 46–47); proof pp.45–46 (PDF 47–48)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_ConvexBandit
import Definitions.Def_BilateralProfitRegular_InitRegular
import Definitions.Def_BilateralProfitRegular_Refinement

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade Classical

/-- **Lemma 6.6 (Refinement and successive elimination)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), pp.44–45 (PDF 46–47); proof pp.45–46 (PDF 47–48). Assume
initialization triggers with the guarantees of Lemma 6.4.

(i) *Refinement.* Fix a candidate `i`, its reference and a valid calibrated parameter `λ`. In any
phase `j` started before `T`, refinement returns `y ∈ 𝒦_i` and `r̂_i` with, except with
probability `1/T`, `max_{𝒦_i} r_λ − ε_j ≤ r̂_i ≤ r_λ(y) + ε_j` (57), for refinement run to
completion.

(ii) *Elimination.* If all calibrations and refinements through a completed phase `j` satisfy
(49) and (57), then `i⋆` survives to phase `j + 1` and every retained and updated reference
`z_i^{(j+1)}` satisfies `µ⋆ − r_{ρ_i^{(j+1)} λ_{z_i^{(j+1)}}}(z_i^{(j+1)}) ≤ 65(η + ε_{j+1})` (58),
`ρ_i^{(j+1)}` the output of the next valid calibration. The same holds for `j = 0`.

**Formalization Note.**
* `ε_j = δ 2^{-j}`. Refinement in phase `j` (Algorithm 8; eq. (56)): `M = ⌈C₀ log(2T)⌉`
  independent runs of ConOpt, each of `n = 4^j ⌈C₀ log⁴(2T)⌉` loss observations; for each run
  the average query `ȳ` and the average observation `L̂`; a run with the smallest `L̂` is selected
  and `r̂ = 1/max{L̂, 1/(10δ)}`. (57) is required of **every** run attaining the minimum (any
  tie-breaking). ConOpt is **any** `n`-query algorithm on `𝒦_i` satisfying (55) with constant
  `C₂` for every observation law satisfying (50) with constant `C₁`; the runs' observations are
  any such law. `C₀` is chosen after `C₁`, `C₂` (p.44). The probability is over the `M`
  independent runs (`multiExp`).
* "Phase `j` started before `T`": `j = 0`, or a run of the previous phase, of
  `4^{j−1}⌈C₀ log⁴(2T)⌉ ≥ 1`-round observations, fits in `T` rounds (the proof's use, "n ≤ 4T").
* A valid calibrated parameter is `λ > 0` with `|log(λ/λ_i)| ≤ 10⁻³√(η/δ)` (eq. (49) for
  `λ = ρλ_z`). The guarantees of Lemma 6.4 enter as `η < δ`, `δ ≤ µ⋆ < 6δ`, the candidate(s)
  valid, and in (ii) `i⋆` any near-optimal candidate (Lemma 6.4(i)); Section 6's standing
  `η ∈ (0, 1)`, `⌈1/η⌉ ≤ T` are kept.
* (ii) is deterministic: phases are encoded by the active sets `A_j` (all candidates at `j = 0`;
  `A_{j+1}` = the candidates of `A_j` with `r̂_i ≥ max_{ℓ ∈ A_j} r̂_ℓ − 10(η + ε_j)`), the
  references `z_j` (`z_0 = w`, `z_{j+1} = y_j` for survivors), multipliers `ρ_j`, outputs `y_j`,
  `r̂_j`; "max over `𝒦_i`" in (57) is written with `∀ x ∈ 𝒦_i`.
* The event of (i) is `RefineGood`; the failure probability is the expectation of its
  indicator over the `M` runs. -/
theorem lemma_6_6 :
    (∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (c : Candidate), η < δ → δ ≤ muStar E → muStar E < 6 * δ → c.Valid E δ →
      ∀ lam : ℝ, 0 < lam → |Real.log (lam / c.param E)| ≤ 1 / 1000 * Real.sqrt (η / δ) →
      ∀ j : ℕ, (j = 0 ∨ phaseLen C₀ T (j - 1) ≤ T) →
      ∀ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω), IsProbabilityMeasure Pω →
      ∀ alg : BanditAlg (ℝ × ℝ) Ω, alg.QueriesIn c.region →
        (∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
          ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
          alg.regret ν Pω (phaseLen C₀ T j) (fun x => 1 / auxProfit E lam x) c.region ≤
            ENNReal.ofReal (C₂ / δ * Real.sqrt (phaseLen C₀ T j) *
              Real.log (2 * (phaseLen C₀ T j : ℝ)) ^ 2)) →
      ∀ ν : ObsEnv (ℝ × ℝ), ν.MeanOn (fun x => 1 / auxProfit E lam x) c.region →
        ν.ValuesIn c.region (Set.Icc 0 (C₁ / δ)) →
        alg.multiExp ν Pω (phaseLen C₀ T j) (numCopies C₀ T)
            (fun hs => if RefineGood E lam δ (acc δ j) c.region hs then 0 else 1) ≤
          ENNReal.ofReal (1 / T)) ∧
    (∀ (η : ℝ), 0 < η → η < 1 →
      ∀ E : Environment, RegularUnit E →
      ∀ (δ : ℝ) (N : ℕ) (cs : Fin N → Candidate),
        η < δ → δ ≤ muStar E → muStar E < 6 * δ → (∀ i, (cs i).Valid E δ) →
      ∀ istar : Fin N, (cs istar).NearOpt E η δ →
      ∀ (A : ℕ → Finset (Fin N)) (z y : ℕ → Fin N → ℝ × ℝ) (ρ rhat : ℕ → Fin N → ℝ),
        A 0 = Finset.univ → (∀ i, z 0 i = (cs i).root) →
        (∀ j i, i ∈ A (j + 1) ↔
          i ∈ A j ∧ ∀ l ∈ A j, rhat j l - 10 * (η + acc δ j) ≤ rhat j i) →
        (∀ j, ∀ i ∈ A (j + 1), z (j + 1) i = y j i) →
        (∀ i, ∀ ρ' : ℝ, CalibValid E η δ (cs i) (cs i).root ρ' →
          muStar E - auxProfit E (ρ' * balance E (cs i).root) (cs i).root ≤
            65 * (η + acc δ 0)) ∧
        ∀ j : ℕ,
          (∀ j' ≤ j, ∀ i ∈ A j',
            CalibValid E η δ (cs i) (z j' i) (ρ j' i) ∧ y j' i ∈ (cs i).region ∧
            (∀ x ∈ (cs i).region,
              auxProfit E (ρ j' i * balance E (z j' i)) x - acc δ j' ≤ rhat j' i) ∧
            rhat j' i ≤ auxProfit E (ρ j' i * balance E (z j' i)) (y j' i) + acc δ j') →
          istar ∈ A (j + 1) ∧
          ∀ i ∈ A (j + 1), ∀ ρ' : ℝ, CalibValid E η δ (cs i) (z (j + 1) i) ρ' →
            muStar E - auxProfit E (ρ' * balance E (z (j + 1) i)) (z (j + 1) i) ≤
              65 * (η + acc δ (j + 1))) := by sorry

end BilateralProfitRegular
