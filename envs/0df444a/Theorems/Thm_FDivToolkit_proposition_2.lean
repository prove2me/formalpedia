-- Prove2me | Theorems.Thm_FDivToolkit_proposition_2
-- name    : FDivToolkit.proposition_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:50.305735+00:00
-- url     : https://prove2.me/theorems/5cf10852-5c2c-473a-8c0b-ea6ffdc8b3eb
-- title:
--   Proposition 2 — a finite $\theta$-th moment gives finite divergence
-- statement:
--   Let $\theta>1$, let $H$ be a generating function with $F(0)<\infty$, and let $\nu$ be a reference model with density $f$ such that, with $\varphi=-\log f$,
--   $$
--   \limsup_{|x|\to\infty}\frac{H(\varphi(x))\mathbf 1_{\mathcal S}(x)}{|x|^\theta}<\infty.
--   $$
--   Let $\eta$ be a distribution on $\mathcal S$, absolutely continuous with respect to $\nu$, with density $g$. Suppose that
--
--   1. $\int_{\mathcal S\cap[-r,r]}F\big(\frac{g(x)}{f(x)}\big)f(x)\,dx<\infty$ for all $r\in(0,\infty)$,
--   2. $\limsup_{|x|\to\infty}g(x)<1$,
--   3. $\int_{\mathcal S}|x|^\theta g(x)\,dx<\infty$.
--
--   Then $D_F(\eta\,|\,\nu)<\infty$.
--
--   Together with Proposition 3, this makes the $\theta$-th moment the cut-off for inclusion in a divergence ball.
--
--   Differences from the source:
--   - encoding: ϕ = −log f, which is +∞ where f = 0, and lim sup_{|x|→∞} H(ϕ(x))1_𝓢(x)/|x|^θ < ∞ with the expression 0 off 𝓢 (footnote 11) → ∃ C x₀, ∀ x ∈ 𝓢 with x₀ ≤ |x|, 0 < f x and H(−log f x) ≤ C|x|^θ; reason: Real.log 0 = 0 is not the paper's value, so positivity is written out; the condition is equivalent to the paper's
--   - encoding: |x| → ∞, the pair of limits x → ∞ and x → −∞ (footnote 8), with lim sup < ∞ → the filter cocompact ℝ, with an eventual bound by a constant; reason: cocompact ℝ is exactly that pair of limits, and a lim sup of a function is finite exactly when the function is eventually bounded
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Proposition 2, p.11

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_fDiv
import Definitions.Def_FDivToolkit_Fh

open MeasureTheory Filter Set
open scoped ENNReal

namespace FDivToolkit

/-- Proposition 2, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.11. Let `θ > 1`. Assume
`F(0) < ∞` and `lim sup_{|x|→∞} H(ϕ(x)) 1_𝓢(x)/|x|^θ < ∞`, where `ϕ = −log f`. Let η be a distribution
on `𝓢`, absolutely continuous with respect to ν, with density `g`. Suppose
`∫_{𝓢∩[−r,r]} F(g(x)/f(x)) f(x) dx < ∞` for all `r ∈ (0, ∞)`, `lim sup_{|x|→∞} g(x) < 1` and
`∫_𝓢 |x|^θ g(x) dx < ∞`. Then `D_F(η|ν) < ∞`.

**Formalization Note.** The paper's `ϕ` is `+∞` where `f = 0`, and the expression in its lim sup is `0`
off `𝓢` (footnote 11). So the lim sup condition says: for `x ∈ 𝓢` with `|x|` large, `f x > 0` and
`H(ϕ(x)) ≤ C |x|^θ`. The radius of the paper's `[−k, k]` is written `r`. -/
theorem proposition_2 {H f g : ℝ → ℝ} {θ : ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f)
    (hθ : 1 < θ) (hF0 : F0 H < ⊤)
    (hϕ : ∃ C x₀ : ℝ, ∀ x ∈ refSupport f, x₀ ≤ |x| →
      0 < f x ∧ H (-Real.log (f x)) ≤ C * |x| ^ θ)
    (hg : IsDensity g) (hac : densityMeasure g ≪ densityMeasure f)
    (hloc : ∀ r : ℝ, 0 < r → ∫⁻ x in refSupport f ∩ Icc (-r) r, divIntegrand (Fbar H) f g x < ⊤)
    (hgtail : ∃ c : ℝ, c < 1 ∧ ∀ᶠ x in cocompact ℝ, g x ≤ c)
    (hmom : ∫⁻ x in refSupport f, ENNReal.ofReal (|x| ^ θ * g x) < ⊤) :
    fDiv (Fbar H) f g < ⊤ := by sorry

end FDivToolkit
