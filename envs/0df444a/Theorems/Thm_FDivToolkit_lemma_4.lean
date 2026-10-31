-- Prove2me | Theorems.Thm_FDivToolkit_lemma_4
-- name    : FDivToolkit.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:53.946432+00:00
-- url     : https://prove2.me/theorems/29736de8-9db7-4d03-adcf-fc852eb6d869
-- title:
--   Lemma 4 — for Weibull-type models, the $H$ of (10) has $F(0)=1$ and satisfies Propositions 1, 2 and 3
-- statement:
--   Let $k>0$ and $\theta>\max\{k,1\}$, let $H$ be the function of (10), and let $\nu$ be a reference model with density $f$, support $\mathcal S=[0,\infty)$ and $\varphi=-\log f\in\Theta(x^k)$. Then:
--
--   1. $F(0)=1$;
--   2. $\limsup_{x\to\infty}H(\varphi(x))/x^\theta<\infty$;
--   3. $\limsup_{y\to\infty}H'(y)/H(y)<\infty$;
--   4. $\liminf_{x\to\infty}H(\varphi(x)-(t+1)\log x-c)/x^t>0$ for all $t\in(1,\theta)$ and $c\in(0,\infty)$;
--   5. Condition (7) is satisfied;
--   6. the assertion of Proposition 1 holds, for every $\kappa>0$: the worst case is finite, the worst-case model has the density (6) for some $(\alpha_1,\alpha_2)\in\mathbb R\times(0,\infty)$, and these parameters are uniquely characterized by $\int g^{wc}=1$ and $D_F(\eta^{wc}\,|\,\nu)=\kappa$;
--   7. the assertion of Proposition 2 holds for this $\theta$: every $\eta$ absolutely continuous with respect to $\nu$, with density $g$, satisfying the local integrability condition, $\limsup_{|x|\to\infty}g(x)<1$ and $\int_{\mathcal S}|x|^\theta g(x)\,dx<\infty$, has $D_F(\eta\,|\,\nu)<\infty$;
--   8. the assertion of Proposition 3 holds for every $t\in(1,\theta)$: every such $\eta$ with $\liminf_{x\to\infty}x^{t+1}g(x)>0$ and $\lim_{x\to\infty}g(x)/f(x)=\infty$ has $D_F(\eta\,|\,\nu)=+\infty$.
--
--   This is the paper's headline for Weibull-type reference models, including the heavy-tailed case $k<1$: worst cases are finite, worst-case densities are explicit, and the $\theta$-th moment is the cut-off for inclusion in a divergence ball.
--
--   Differences from the source:
--   - reading: "the assertions of Propositions 1, 2 and 3 hold true" → the conclusions of the three propositions written out as clauses for this H and f, with their hypotheses on H and ν discharged; reason: this is what the sentence says; the hypotheses on η remain hypotheses, and κmax = ∞ as sup 𝓢 = ∞
--   - generalization: the worst case in (4) is finite → for every κ > 0, every g in the ball has x g(x) integrable, and the set of means is bounded above; reason: a real supremum would be 0 on an unbounded set, and a supremum over integrable models only would drop heavy-tailed models; the Lean clause implies that the supremum over the ball is finite
--   - reading: the worst-case model η^wc in (4) has the density (6) → g^wc is in the ball, its mean is the greatest mean, and every member of the ball with that mean equals g^wc almost everywhere; reason: the proof on p.32 says "the maximizer in (4) is unique"
--   - encoding: ϕ = −log f, which is +∞ where f = 0, with lim sup H(ϕ(x))/x^θ < ∞ and lim inf H(ϕ(x) − (t+1) log x − c)/x^t > 0 → ∃ C, eventually 0 < f x and H(−log f x) ≤ C x^θ; and ∃ ε > 0, eventually f x = 0 or ε x^t ≤ H(−log f x − (t+1) log x − c); reason: Real.log 0 = 0 is not the paper's value; the conditions are equivalent to the paper's
--   - encoding: lim sup_{y→∞} H′(y)/H(y) < ∞ → ∃ C, eventually H′(y) ≤ C H(y); reason: H > 0 on (0, ∞), so the two conditions are equivalent
--   - encoding: lim_{x→∞} g(x)/f(x) = ∞ and lim inf_{x→∞} x^{t+1}g(x) > 0 → ∀ M, eventually M f x < g x; and ∃ δ > 0, eventually δ ≤ x^{t+1} g x; reason: no quotient, since Lean's x/0 = 0 is not the paper's value
--   - encoding: |x| → ∞, the pair of limits x → ∞ and x → −∞ (footnote 8), with lim sup < ∞ → the filter cocompact ℝ, with an eventual bound by a constant; reason: cocompact ℝ is exactly that pair of limits, and a lim sup of a function is finite exactly when the function is eventually bounded
--   - encoding: L = lim_{y→−∞} H(y) and the test x > L → the test x ∈ range H; reason: range H = (L, ∞) for admissible H, as proved in the mission's sanity file
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
--   - encoding: 𝓢 = [0, ∞) as the support of ν → refSupport f = Ici 0, the closed support; reason: the paper's 𝓢 is the support of ν
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Lemma 4, p.13, in the setting of §3.1, p.12

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Cond7
import Definitions.Def_FDivToolkit_gwc
import Definitions.Def_FDivToolkit_weibullH
import Definitions.Def_FDivToolkit_WeibullTail

open MeasureTheory Filter Set
open scoped ENNReal

namespace FDivToolkit

/-- Lemma 4, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.13, in the Weibull setting of
§3.1, p.12: `𝓢 = [0, ∞)`, `ϕ = −log f ∈ Θ(x^k)` with `k > 0`, `θ > max{k, 1}`, and `H` the function of
(10). It holds that `F(0) = 1`, that `lim sup_{x→∞} H(ϕ(x))/x^θ < ∞`, that
`lim sup_{y→∞} H′(y)/H(y) < ∞` and that `lim inf_{x→∞} H(ϕ(x) − (t+1) log x − c)/x^t > 0` for all
`t ∈ (1, θ)` and `c ∈ (0, ∞)`. Moreover, Condition (7) is satisfied. Thus, the assertions of
Propositions 1, 2 and 3 hold true.

**Formalization Note.** The conclusions of the three propositions are written out in the last three
clauses, in the same form as `proposition_1`, `proposition_2` and `proposition_3`. Proposition 1 is
stated for every `κ > 0`, since `𝓢` is unbounded above and so `κmax = ∞`. For `x ≥ 0` the formula in
Proposition 2's lim sup condition is the second clause here. -/
theorem lemma_4 {k θ : ℝ} (hk : 0 < k) (hθ : max k 1 < θ) {H f : ℝ → ℝ} (hHdef : H = weibullH k θ)
    (hf : IsRefModel f) (hS : refSupport f = Ici 0) (hΘ : WeibullTail f k) :
    F0 H = 1 ∧
    (∃ C : ℝ, ∀ᶠ x in atTop, 0 < f x ∧ H (-Real.log (f x)) ≤ C * x ^ θ) ∧
    (∃ C : ℝ, ∀ᶠ y in atTop, deriv H y ≤ C * H y) ∧
    (∀ t ∈ Ioo 1 θ, ∀ c : ℝ, 0 < c → ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ x in atTop,
      f x = 0 ∨ ε * x ^ t ≤ H (-Real.log (f x) - (t + 1) * Real.log x - c)) ∧
    Cond7 H f ∧
    (∀ κ : ℝ, 0 < κ →
      (∀ g ∈ ball H f κ, Integrable fun x => x * g x) ∧ BddAbove (meanSet H f κ) ∧
      ∃ α : ℝ × ℝ, IsWcParam H f κ α ∧
        gwc H f α ∈ ball H f κ ∧
        IsGreatest (meanSet H f κ) (∫ x, x * gwc H f α x) ∧
        (∀ g ∈ ball H f κ, ∫ x, x * g x = ∫ x, x * gwc H f α x → g =ᵐ[volume] gwc H f α) ∧
        ∀ β : ℝ × ℝ, IsWcParam H f κ β → β = α) ∧
    (∀ g : ℝ → ℝ, IsDensity g → densityMeasure g ≪ densityMeasure f →
      (∀ r : ℝ, 0 < r → ∫⁻ x in refSupport f ∩ Icc (-r) r, divIntegrand (Fbar H) f g x < ⊤) →
      (∃ c : ℝ, c < 1 ∧ ∀ᶠ x in cocompact ℝ, g x ≤ c) →
      ∫⁻ x in refSupport f, ENNReal.ofReal (|x| ^ θ * g x) < ⊤ →
      fDiv (Fbar H) f g < ⊤) ∧
    (∀ t ∈ Ioo 1 θ, ∀ g : ℝ → ℝ, IsDensity g → densityMeasure g ≪ densityMeasure f →
      (∃ δ : ℝ, 0 < δ ∧ ∀ᶠ x in atTop, δ ≤ x ^ (t + 1) * g x) →
      (∀ M : ℝ, ∀ᶠ x in atTop, M * f x < g x) →
      fDiv (Fbar H) f g = ⊤) := by sorry

end FDivToolkit
