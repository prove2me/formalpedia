-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_proposition_1
-- name    : CappeKLUCB.Empirical.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:57.804281+00:00
-- url     : https://prove2.me/theorems/cae89523-4d6e-4aa4-bc01-bd34500cbee9
-- title:
--   Proposition 1, p. 20 — ℙ{U(ν̂ₙ, ε) ≤ E(ν₀)} ≤ ℙ{𝒦_inf(ν̂ₙ, E(ν₀)) ≥ ε} ≤ e(n + 2)exp(−nε)
-- statement:
--   Let $\nu_0$ be a probability distribution on $[0,1]$, not necessarily finitely supported, with $\mathrm E(\nu_0)\in(0,1)$. Let $X_1,\dots,X_n$ ($n\ge1$) be independent random variables with common distribution $\nu_0$, let $\hat\nu_n = \frac1n\sum_{k=1}^n\delta_{X_k}$ be their empirical distribution, and let
--   $$U(\hat\nu_n,\varepsilon) = \sup\bigl\{\mathrm E(\nu') : \nu'\in\mathfrak M_1(\mathrm{Supp}(\hat\nu_n)\cup\{1\}) \text{ and } \mathrm{KL}(\hat\nu_n,\nu')\le\varepsilon\bigr\} \qquad (15)$$
--   be the empirical-likelihood upper confidence bound with the value $1$ added to the support. Then for every $\varepsilon>0$,
--   $$\mathbb P\bigl\{U(\hat\nu_n,\varepsilon)\le\mathrm E(\nu_0)\bigr\} \le \mathbb P\bigl\{\mathcal K_{\inf}(\hat\nu_n,\mathrm E(\nu_0))\ge\varepsilon\bigr\} \le e\,(n+2)\exp(-n\varepsilon),$$
--   where $\mathcal K_{\inf}$ is defined in terms of the model $\mathcal F$ of finitely supported distributions over $[0,1]$.
--
--   This is a non-asymptotic coverage guarantee for the empirical-likelihood upper confidence bound on bounded observations; in the regret analysis it controls the sum $\sum_t\mathbb P\{\mu^\dagger\ge U_{a^\star}(t)\}$ of (10) (Fact 1), and it holds without assuming that $\nu_0$ is finitely supported.
--
--   **Formalization Note** The sample is the first $n$ terms $Y_0,\dots,Y_{n-1}$ of a real sequence of functions on a probability space; only these $n$ are assumed measurable, mutually independent and $\nu_0$-distributed. $\nu_0\in\mathfrak M_1([0,1])$ is written as "$\nu_0$ is a probability measure with $\nu_0([0,1]^c)=0$". The probabilities are outer probabilities of the events, whose measurability is not asserted. KL and $\mathcal K_{\inf}$ are valued in $[0,+\infty]$, and $e\,(n+2)\exp(-n\varepsilon)$ is embedded in $[0,+\infty]$.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 20, Proposition 1, with U of (15), p. 19

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- Proposition 1, Cappé et al., arXiv:1210.1136v4, p. 20: for `n` i.i.d. observations from a law
`ν₀` on `[0, 1]` with `E(ν₀) ∈ (0, 1)` and every `ε > 0`,
`ℙ{U(ν̂_n, ε) ≤ E(ν₀)} ≤ ℙ{𝒦_inf(ν̂_n, E(ν₀)) ≥ ε} ≤ e (n + 2) exp(−n ε)`, with `U` of (15) and
`𝒦_inf` for the model `ℱ`. -/
theorem proposition_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν₀ : Measure ℝ) [IsProbabilityMeasure ν₀] (h01 : ν₀ (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmean : mean ν₀ ∈ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (hn : 1 ≤ n) (Y : ℕ → Ω → ℝ) (hYm : ∀ k < n, Measurable (Y k))
    (hind : iIndepFun (fun k : Fin n => Y k) P) (hlaw : ∀ k < n, P.map (Y k) = ν₀)
    (ε : ℝ) (hε : 0 < ε) :
    P {ω | elUpper (empSupp (fun k => Y k ω) n) (empMeasure (fun k => Y k ω) n) ε ≤ mean ν₀}
        ≤ P {ω | ENNReal.ofReal ε ≤ Kinf (empMeasure (fun k => Y k ω) n) (mean ν₀)} ∧
      P {ω | ENNReal.ofReal ε ≤ Kinf (empMeasure (fun k => Y k ω) n) (mean ν₀)}
        ≤ ENNReal.ofReal (Real.exp 1 * ((n : ℝ) + 2) * Real.exp (-((n : ℝ) * ε))) := by sorry

end CappeKLUCB.Empirical
