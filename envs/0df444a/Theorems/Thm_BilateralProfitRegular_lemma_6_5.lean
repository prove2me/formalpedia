-- Prove2me | Theorems.Thm_BilateralProfitRegular_lemma_6_5
-- name    : BilateralProfitRegular.lemma_6_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:20:44.194275+00:00
-- url     : https://prove2.me/theorems/4de32a35-108c-49bd-8033-63ec7c01cd80
-- title:
--   Lemma 6.5 — calibration with $O(\log T/\eta)$ regret, and unbiased bounded loss observations of $1/r_\lambda$
-- statement:
--   Assume the guarantees of Lemma 6.4's event with a trigger: $\eta<\delta$, $\delta\le\mu^\star<6\delta$, and a valid candidate $(\mathcal K_i,w_i,\theta_i,\widehat P(w_i))$. Let $z\in\mathcal K_i$ be a reference, and let $\eta\in(0,1)$ with $\lceil1/\eta\rceil\le T$. There is a universal constant $C$ such that the following hold.
--
--   **(i) Calibration.** There is a procedure, built from the known data, with the following properties:
--
--   - it posts only prices in $\mathcal T$;
--   - it incurs expected regret at most $C\log(T)/\eta$;
--   - except with probability at most $1/T$, it returns $\rho>0$ with
--   $$\Big|\log\frac{\rho\lambda_z}{\lambda_i}\Big|\le10^{-3}\sqrt{\eta/\delta}. \tag{49}$$
--
--   **(ii) Loss observations.** Let $\rho$ satisfy (49), let $\lambda=\rho\lambda_z$ and $L=1/r_\lambda$. Each query $x\in\mathcal K_i$ admits an observation procedure with the following properties:
--
--   - it uses at least one trading round;
--   - its output $Y_x$ satisfies $0\le Y_x\le C/\delta$ and $\mathbb E[Y_x]=L(x)$;
--   - its expected number of rounds is at most $C/\delta$;
--   - every price pair $y$ it posts lies in $\mathcal T$ and satisfies
--   $$\mu^\star-\mu(y)\le C\big(\mu^\star-r_\lambda(z)\big)+C\delta^2\big(L(x)-\min_{\mathcal K_i}L\big). \tag{51}$$
--
--   The procedures use fresh randomness and fresh valuations, so these are also the conditional statements given the past and $x$.
--
--   Differences from the source:
--   - generalization: "Assume the guarantees of the high probability event in Lemma 6.4 hold, with Initialize regular triggering"; a candidate of its list → any candidate satisfying `Valid` with $\eta<\delta$, $\delta\le\mu^\star<6\delta$ (not necessarily output by Algorithm 7); reason: the proof uses only these properties; on Lemma 6.4's event every listed candidate satisfies them
--   - encoding: "can be implemented", "admits an observation"; "$\mathbb E[Y_x\mid\text{past},x]$", "conditionally on the choice of $x$ and the history" → there exist sampling procedures, chosen from the known data before the environment; statements for a fixed $x$; reason: the procedures use fresh randomness and valuations, so conditioning on the past changes nothing
--   - encoding: "incur $O(\log(T)/\eta)$ regret"; "every price pair posted … satisfies (51)" → expected sum of $\mu^\star-\mu(y)$ over posted $y$; (51) and $y\in\mathcal T$ for every price the procedure can post (every seed, every history); reason: regret is the expected sum of gaps (p.4); the static form is the stronger one
--   - encoding: independent regular seller and buyer distributions on $[0,1]$ with strictly positive densities (§2, §6) → `RegularUnit E` for a published `Environment` `E` (supports $[0,1]$, `E.Regular`); $P$, $\mu$ from the joint law `E.prior`, $F_s,F_b$ = `E.cdfS`, `E.cdfB`; reason: the same class: Definitions 2.1–2.2 with the standing positivity of the densities; the valuation laws are the environment's
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Lemma 6.5, p.41 (PDF 43); proof pp.41–43 (PDF 43–45)

import Mathlib
import Definitions.Def_BilateralProfitRegular_Stochastic
import Definitions.Def_BilateralProfitRegular_Auxiliary
import Definitions.Def_BilateralProfitRegular_Proc
import Definitions.Def_BilateralProfitRegular_InitRegular

namespace BilateralProfitRegular

open MeasureTheory MechanismDesign.BilateralTrade

/-- **Lemma 6.5 (Convex loss observations)**, Brüstle, di Gregorio, Fusco, Leonardi (manuscript,
sha256 e91e8127…), p.41 (PDF 43); proof pp.41–43 (PDF 43–45). Assume the guarantees of the
high-probability event of Lemma 6.4 hold with a trigger; fix a candidate `i` and a reference
`z ∈ 𝒦_i`.

(i) *Calibration.* Calibration can be implemented so as to incur `O(log(T)/η)` regret, returning a
multiplier `ρ` such that, except with probability at most `1/T`,
`|log(ρλ_z/λ_i)| ≤ 10⁻³ √(η/δ)` (49).

(ii) *Loss observations.* For a constant `C` and `ρ` satisfying (49), set `λ = ρλ_z` and
`L = 1/r_λ`. Each query `x ∈ 𝒦_i` admits an observation `Y_x` using at least one trading round at
prices in `𝒯`, with `0 ≤ Y_x ≤ C/δ` and `E[Y_x | past, x] = L(x)` (50), with expected number of
trading rounds at most `C/δ`; every price pair `y` posted to produce `Y_x` satisfies
`µ⋆ − µ(y) ≤ C(µ⋆ − r_λ(z)) + Cδ²(L(x) − min_{𝒦_i} L)` (51).

**Formalization Note.**
* "The guarantees of Lemma 6.4" enter as the hypotheses the proof uses: `η < δ`,
  `δ ≤ µ⋆ < 6δ`, and candidate `i` valid (`Candidate.Valid`), for an arbitrary candidate
  `(𝒦, w, θ, P̂(w))` and `z ∈ 𝒦`, not only for those output by Algorithm 7. Section 6's standing
  assumptions `η ∈ (0, 1)`, `K = ⌈1/η⌉ ≤ T` are kept.
* "Can be implemented" / "admits": there exist procedures, chosen from the known data
  (`T, η, δ`, the candidate, `z`, and in (ii) `ρ` and `x`) before the environment, which they see
  only through trade bits. A procedure uses fresh randomness and fresh valuations, so the
  conditional statements "given the past and `x`" are statements about the procedure for a fixed
  `x`.
* Regret of a procedure: `E[∑_{posted y} (µ⋆ − µ(y))]`. The calibration failure event includes
  "no output" and `ρ ≤ 0`. `min_{𝒦_i} L` is `sInf (L '' 𝒦_i)`.
* One constant `C` serves (i) and (ii); it is universal (chosen before everything else). -/
theorem lemma_6_5 :
    ∃ C : ℝ, 0 < C ∧
      (∀ (T : ℕ) (η : ℝ), 0 < η → η < 1 → gridK η ≤ T →
        ∀ (δ : ℝ) (c : Candidate) (z : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (cal : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → η < δ → δ ≤ muStar E → muStar E < 6 * δ →
            c.Valid E δ → z ∈ c.region →
            cal.QueriesIn triT ∧
            cal.expCost (P E) Pω (fun y => muStar E - mu E y) ≤
              ENNReal.ofReal (C * Real.log T / η) ∧
            Proc.law Pω {x | ¬ ∃ ρ, cal.out (P E) x.1 x.2 = some ρ ∧ CalibValid E η δ c z ρ} ≤
              ENNReal.ofReal (1 / T)) ∧
      (∀ (η δ : ℝ) (c : Candidate) (z : ℝ × ℝ) (ρ : ℝ) (x : ℝ × ℝ),
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
          (obs : Proc (ℝ × ℝ) ℝ Ω),
          ∀ E : Environment, RegularUnit E → 0 < η → η < 1 → η < δ → δ ≤ muStar E →
            muStar E < 6 * δ → c.Valid E δ → z ∈ c.region → CalibValid E η δ c z ρ →
            x ∈ c.region →
            obs.QueriesFirst ∧
            obs.OutputsIn (Set.Icc 0 (C / δ)) ∧
            obs.expRounds (P E) Pω ≤ ENNReal.ofReal (C / δ) ∧
            Proc.law Pω {y | obs.out (P E) y.1 y.2 = none} = 0 ∧
            ∫ y, (obs.out (P E) y.1 y.2).getD 0 ∂(Proc.law Pω) =
              1 / auxProfit E (ρ * balance E z) x ∧
            ∀ ω h y, obs.step ω h = Sum.inl y →
              y ∈ triT ∧
              muStar E - mu E y ≤
                C * (muStar E - auxProfit E (ρ * balance E z) z) +
                  C * δ ^ 2 * (1 / auxProfit E (ρ * balance E z) x -
                    sInf ((fun a => 1 / auxProfit E (ρ * balance E z) a) '' c.region))) := by sorry

end BilateralProfitRegular
