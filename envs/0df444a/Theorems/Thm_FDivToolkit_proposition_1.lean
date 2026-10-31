-- Prove2me | Theorems.Thm_FDivToolkit_proposition_1
-- name    : FDivToolkit.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:24:37.868255+00:00
-- url     : https://prove2.me/theorems/c5a5bdcf-201d-4fd0-920a-d73f226be026
-- title:
--   Proposition 1 — the worst case is finite with the explicit density (6)
-- statement:
--   Let $H$ be a generating function, $L=\lim_{y\to-\infty}H(y)\in[-\infty,0)$, and $\nu$ a reference model with density $f$ satisfying (5). Then the worst case in (4) is finite for every $\kappa>0$, and there exists $\kappa_{\max}\in(0,\infty]$ such that for all $\kappa\in(0,\kappa_{\max})$ there exists $(\alpha_1,\alpha_2)\in\mathbb R\times(0,\infty)$ with the following properties. The worst-case model has the density
--   $$
--   g^{wc}(x)=\mathbf 1_{\{\alpha_1+\alpha_2x>L\}}\exp\!\big(H^{-1}(\alpha_1+\alpha_2x)\big)f(x),\qquad x\in\mathcal S.
--   $$
--   Moreover, $(\alpha_1,\alpha_2)$ is uniquely characterized among $\mathbb R\times(0,\infty)$ by the conditions that $g^{wc}$ integrates to $1$ and that $D_F(\eta^{wc}\,|\,\nu)=\kappa$. If $\sup\mathcal S=\infty$, then $\kappa_{\max}=\infty$.
--
--   This is the worst-case component of the toolkit: it reduces an infinite-dimensional problem to two parameters, with the density explicit through $H^{-1}$.
--
--   Differences from the source:
--   - generalization: the worst case in (4) is finite → for every κ > 0, every g in the ball has x g(x) integrable, and the set of means is bounded above; reason: a real supremum would be 0 on an unbounded set, and a supremum over integrable models only would drop heavy-tailed models; the Lean clause implies that the supremum over the ball is finite
--   - reading: the worst-case model η^wc in (4) has the density (6) → g^wc is in the ball, its mean is the greatest mean, and every member of the ball with that mean equals g^wc almost everywhere; reason: the proof on p.32 says "the maximizer in (4) is unique"
--   - encoding: L = lim_{y→−∞} H(y) and the test x > L → the test x ∈ range H; reason: range H = (L, ∞) for admissible H, as proved in the mission's sanity file
--   - encoding: distributions ν, η on 𝓢 with densities f, g → functions f, g : ℝ → ℝ with IsRefModel f and IsDensity g, the distributions being densityMeasure f and densityMeasure g, and integrals over 𝓢 written over ℝ where f or g vanishes off 𝓢; reason: the paper uses its distributions only through their densities; measurability is the standing convention of the field, and f = 0 off 𝓢 by footnote 2
--   - encoding: sup 𝓢 = ∞ → ¬ BddAbove (refSupport f); reason: same statement
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), Proposition 1, p.8

import Definitions.Def_FDivToolkit_IsRefModel
import Definitions.Def_FDivToolkit_Cond5
import Definitions.Def_FDivToolkit_gwc

open MeasureTheory
open scoped ENNReal

namespace FDivToolkit

/-- Proposition 1, Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), p.8. Assume (5). Then the
worst case in (4) is finite, and there is `κmax ∈ (0, ∞]` such that for all `κ ∈ (0, κmax)` there are
`(α₁, α₂) ∈ ℝ × (0, ∞)` for which the worst-case model has the density `g^wc` of (6); these parameters
are uniquely characterized by `∫ g^wc = 1` and `D_F(η^wc|ν) = κ`. If `sup 𝓢 = ∞` then `κmax = ∞`.

**Formalization Note.** "Finite" is stated for every `κ > 0` as: every member of the ball has an
integrable `x g(x)`, and the means are bounded above. "The worst-case model has the density `g^wc`"
is: `g^wc` is in the ball, its mean is the greatest mean, and every member of the ball with that mean
equals `g^wc` almost everywhere (proof, p.32: "the maximizer in (4) is unique"). -/
theorem proposition_1 {H f : ℝ → ℝ} (hH : IsAdmissibleH H) (hf : IsRefModel f) (h5 : Cond5 H f) :
    (∀ κ : ℝ, 0 < κ →
      (∀ g ∈ ball H f κ, Integrable fun x => x * g x) ∧ BddAbove (meanSet H f κ)) ∧
    ∃ κmax : ℝ≥0∞, 0 < κmax ∧ (¬ BddAbove (refSupport f) → κmax = ⊤) ∧
      ∀ κ : ℝ, 0 < κ → ENNReal.ofReal κ < κmax →
        ∃ α : ℝ × ℝ, IsWcParam H f κ α ∧
          gwc H f α ∈ ball H f κ ∧
          IsGreatest (meanSet H f κ) (∫ x, x * gwc H f α x) ∧
          (∀ g ∈ ball H f κ, ∫ x, x * g x = ∫ x, x * gwc H f α x → g =ᵐ[volume] gwc H f α) ∧
          ∀ β : ℝ × ℝ, IsWcParam H f κ β → β = α := by sorry

end FDivToolkit
