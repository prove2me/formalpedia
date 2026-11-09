-- Prove2me | Theorems.Thm_BosonicLearn_proposition_1
-- name    : BosonicLearn.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:45.014734+00:00
-- url     : https://prove2.me/theorems/d9a4ce13-f895-4d72-aaee-13a8c583c089
-- title:
--   Proposition 1 — posterior anti-concentration reduces to a lower bound on $\mathbb E_Z L_{\Phi_{X_0}(Z)}$
-- statement:
--   Let $\mathcal T_X$ $(X\in\mathrm{Herm}_0(n))$ be a statistical model on an outcome space with likelihoods $\mathcal T_X(x)$ (densities with respect to a common σ-finite measure, jointly measurable), let $\mu$ be the prior (32) and $\nu_x$ the posterior. Write $L_X(x)=\mathcal T_X(x)/\mathcal T_{X_0}(x)$ and $B_{\Phi,b}(X_0)=\Phi_{X_0}(B_{\mathrm{op},b}(0))$.
--
--   For every $b\in(0,0.1]$ there are $a_0,c>0$, $\xi_0\in(0,1/32)$ and $n_1$ such that for all $a\in(0,a_0]$, $n\ge n_1$, $\xi\in(0,\xi_0]$ and $X_0\in G_{\mathrm{good}}$: with probability at least $1-e^{-n^2}$ over $x\sim\mathcal T_{X_0}$,
--
--   $$\frac{\nu_x(B_{\mathrm{tr},na}(X_0))}{\nu_x(B_{\Phi,b}(X_0))}\le e^{-cn^2}\Big(\mathop{\mathbb E}_{Z\sim\mathrm{Unif}(B_{\mathrm{op},b}(0))}L_{\Phi_{X_0}(Z)}(x)\Big)^{-1}.$$
--
--   It reduces the lower bound to showing that the averaged likelihood ratio is not exponentially small.
--
--   Differences from the source:
--   - generalization: T_X the transcript likelihood of an adaptive single-copy scheme on ρ_{R_X} → any statistical model with jointly measurable likelihoods p_X with respect to a σ-finite reference measure; reason: the proof uses only Bayes' rule, Markov's inequality and Lemmas 8–9; the transcript model is one such model
--   - reading: "a and b are sufficiently small positive constants" → for every b ∈ (0, 0.1] there is a₀ with the claim for all a ∈ (0, a₀]; reason: the proof of Theorem 5 fixes b = 0.1 and a small; the claim is monotone in a
--   - encoding: the ratio bound (54) with exp(−Ω(n²)) → the bound multiplied out, ∫_{B_tr} p_X(x)µ(dX) · E_Z p_{Φ(Z)}(x) ≤ e^{−cn²} p_{X₀}(x) ∫_{B_Φ} p_X(x)µ(dX), with ∃ c > 0 and n ≥ n₁; reason: the posterior normalizations cancel and L_X = p_X/p_{X₀}; no division by a possibly zero quantity
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, Proposition 1, Eqs. (53)–(54), p. 33

import Mathlib
import Definitions.Def_BosonicLearn_PhiMap
import Definitions.Def_BosonicLearn_Ggood
import Definitions.Def_BosonicLearn_herm0Ball
import Definitions.Def_BosonicLearn_priorMu

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Proposition 1 (reduction of posterior anti-concentration to a likelihood-ratio bound).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, Proposition 1, Eqs. (53)–(54), p. 33: "Fix X_0 ∈ G_good. For any X ∈ G_supp and outcomes x, define the
likelihood ratio L_X(x) := T_X(x)/T_{X_0}(x). Then, with probability at least 1 − e^{−n²} over x ∼ T_{X_0},
ν_x(B_{tr,na}(X_0))/ν_x(B_{Φ,b}(X_0)) ≤ exp(−Ω(n²)) (E_{Z∼Unif(B_{op,b}(0))} L_{Φ_{X_0}(Z)}(x))^{−1}."
Here "a and b are sufficiently small positive constants" (p. 33), `ν_x` is the posterior (33) under the prior `µ`
(32), and `B_{Φ,b}(X_0) = Φ_{X_0}(B_{op,b}(0))` (p. 33).

Statistical model: an outcome space `Ω` with a σ-finite reference measure, and likelihoods `T_X = p_X · ref`
(`p` jointly measurable, each `T_X` a probability measure). For every `b ∈ (0, 0.1]` there are `a₀, c > 0`,
`ξ₀ ∈ (0, 1/32)` and `n₁` such that for all `a ∈ (0, a₀]`, `n ≥ n₁`, `ξ ∈ (0, ξ₀]` and `X₀ ∈ G_good`, with
`T_{X₀}`-probability at least `1 − e^{−n²}`,
$$\int_{B_{tr,na}(X_0)} p_X(x)\,µ(dX)\cdot \mathbb E_{Z}\, p_{Φ_{X_0}(Z)}(x) \le e^{-cn^2}\, p_{X_0}(x) \int_{B_{Φ,b}(X_0)} p_X(x)\,µ(dX).$$

**Formalization Note.** Dividing by `∫_{B_{Φ,b}} p_X(x)µ(dX)·p_{X_0}(x)·E_Z p_{Φ(Z)}(x)` gives (54): the posterior
normalizations cancel in the ratio and `L_X = p_X/p_{X_0}`. -/
theorem proposition_1 :
    ∀ b : ℝ, 0 < b → b ≤ 1 / 10 →
      ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ c : ℝ, 0 < c ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ξ₀ < 1 / 32 ∧ ∃ n₁ : ℕ,
        ∀ a : ℝ, 0 < a → a ≤ a₀ → ∀ n : ℕ, n₁ ≤ n → ∀ ξ : ℝ, 0 < ξ → ξ ≤ ξ₀ → ∀ X₀ ∈ Ggood n,
        ∀ (Ω : Type) [MeasurableSpace Ω] (ref : Measure Ω) [SigmaFinite ref]
          (p : Herm0 n → Ω → ℝ≥0∞), Measurable (Function.uncurry p) →
          (∀ X, IsProbabilityMeasure (ref.withDensity (p X))) →
          ENNReal.ofReal (1 - Real.exp (-(n : ℝ) ^ 2)) ≤ (ref.withDensity (p X₀))
            {x | (∫⁻ X in herm0Ball 1 X₀ (n * a), p X x ∂(priorMu n)) *
                  (∫⁻ Z, p (PhiMap X₀ ξ Z) x ∂(cond (Measure.addHaar : Measure (Herm0 n)) (herm0Ball ⊤ 0 b)))
                ≤ ENNReal.ofReal (Real.exp (-(c * (n : ℝ) ^ 2))) * p X₀ x *
                  ∫⁻ X in PhiMap X₀ ξ '' herm0Ball ⊤ 0 b, p X x ∂(priorMu n)} := by sorry

end BosonicLearn
