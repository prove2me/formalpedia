-- Prove2me | Theorems.Thm_DataDepProb_Discrete_lemma_4_8
-- name    : DataDepProb.Discrete.lemma_4_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:11:34.851194+00:00
-- url     : https://prove2.me/theorems/c8a4e47c-eb6e-460f-a47a-213c336c0de9
-- title:
--   Lemma 4.8 — amplification by one sample: $\mathrm{TV}\le\delta_n$, $\chi^2\le4\delta_n^2$, and the two expectation comparisons
-- statement:
--   Let $n\ge1$, $D\in\Delta_d$, $S\sim D^n$ and $\delta_n=\sqrt{(d-1)/(2n(n+1))}$. Then
--   $$\mathrm{TV}\big(L(\mathrm{Amp}(S)),D^{n+1}\big)\le\delta_n,\qquad \chi^2\big(L(\mathrm{Amp}(S))\,\|\,D^{n+1}\big)\le4\delta_n^2 .$$
--   Consequently, let $(\bar S,\bar Y)\sim D^{n+1}$ and let $F$ be a randomized procedure whose internal coins are independent of its input and have the same distribution in both experiments. Then $|EF(\mathrm{Amp}(S))-EF(\bar S,\bar Y)|\le L\delta_n$ if $0\le F\le L$, and $|EF(\mathrm{Amp}(S))-EF(\bar S,\bar Y)|\le2\delta_n\sqrt{EF(\bar S,\bar Y)^2}$ whenever $EF(\bar S,\bar Y)^2<\infty$.
--
--   Amplification turns a sample of size $n$ into a pair that is almost an i.i.d. sample of size $n+1$; the lemma quantifies "almost", and the estimator's analysis pays $\delta_n$ for each amplification.
--
--   Differences from the source:
--   - encoding: $[d]$, $L(\mathrm{Amp}(S))$, $D^{n+1}$ → `Fin d`; explicit finite laws `ampLaw n D`, `pairLaw n D` on `(Fin n → Fin d) × Fin d`; reason: the same distributions.
--   - encoding: $n$ implicit → hypothesis $1\le n$; reason: amplification copies an entry and is undefined for $n=0$.
--   - encoding: TV as $\frac12\int|f-g|$ for densities → densities with respect to $\mu+\nu$; reason: one dominating measure for any pair.
--   - reading: randomized procedure $F$ with independent coins → a jointly measurable $F(z,\omega)$, coins $\omega\sim\xi$ for an arbitrary probability measure $\xi$, expectations under (input law) $\otimes\,\xi$; reason: independence and equal coin law in both experiments.
--   - reading: $EF(\bar S,\bar Y)^2<\infty$ and $\sqrt{EF(\bar S,\bar Y)^2}$ → integrability and integral of $F^2$ under $D^{n+1}\otimes\xi$; reason: the bound comes from Fact 4.4 with $E[F^2]$.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 9, Lemma 4.8 (proof pp. 30–31, §A.6)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence
import Definitions.Def_DataDepProb_Discrete_Amp

open MeasureTheory

namespace DataDepProb.Discrete

/-- Lemma 4.8 (amplification by one sample, p. 9). Let `n ≥ 1`, `D ∈ ∆_d`, `S ∼ D^n` and
`δ_n = √((d − 1)/(2n(n + 1)))`. Then `TV(L(Amp(S)), D^{n+1}) ≤ δ_n` and
`χ²(L(Amp(S))‖D^{n+1}) ≤ 4δ_n²`. Consequently, for a randomized procedure `F(z, ω)` whose coins
`ω ∼ ξ` are independent of its input `z ∈ [d]^n × [d]`, with the same law `ξ` in both experiments:
`|E F(Amp(S)) − E F(S̄, Ȳ)| ≤ L δ_n` if `0 ≤ F ≤ L`, and
`|E F(Amp(S)) − E F(S̄, Ȳ)| ≤ 2δ_n √(E F(S̄, Ȳ)²)` whenever `E F(S̄, Ȳ)² < ∞`,
where `(S̄, Ȳ) ∼ D^{n+1}`. -/
theorem lemma_4_8 {n d : ℕ} (hn : 1 ≤ n) (D : Fin d → ℝ) (hD : D ∈ simplex d) :
    tv (ampLaw n D) (pairLaw n D) ≤ deltaN n d ∧
    chiSq (ampLaw n D) (pairLaw n D) ≤ ENNReal.ofReal (4 * deltaN n d ^ 2) ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (ξ : Measure Ω) [IsProbabilityMeasure ξ]
      (F : (Fin n → Fin d) × Fin d → Ω → ℝ), Measurable (Function.uncurry F) →
      (∀ L : ℝ, (∀ z ω, 0 ≤ F z ω ∧ F z ω ≤ L) →
        |∫ p, F p.1 p.2 ∂((ampLaw n D).prod ξ) - ∫ p, F p.1 p.2 ∂((pairLaw n D).prod ξ)|
          ≤ L * deltaN n d) ∧
      (Integrable (fun p => F p.1 p.2 ^ 2) ((pairLaw n D).prod ξ) →
        |∫ p, F p.1 p.2 ∂((ampLaw n D).prod ξ) - ∫ p, F p.1 p.2 ∂((pairLaw n D).prod ξ)|
          ≤ 2 * deltaN n d * Real.sqrt (∫ p, F p.1 p.2 ^ 2 ∂((pairLaw n D).prod ξ))) := by sorry

end DataDepProb.Discrete
