-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_prop7_34_usc_epsilon_selector
-- name    : BertsekasShreve.SemicontSelection.prop7_34_usc_epsilon_selector
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:56.348797+00:00
-- url     : https://prove2.me/theorems/a260bea1-f88e-4407-856b-25effc6eaf46
-- title:
--   Proposition 7.34 — Borel-measurable $\varepsilon$-optimal selectors for upper semicontinuous costs
-- statement:
--   Let $X$ be a metrizable space, $Y$ a separable metrizable space, $D$ an open subset of $X\times Y$, and $f:D\to R^*$ upper semicontinuous (in the relative topology of $D$). For $x\in\operatorname{proj}_X(D)$ let $D_x=\{y\mid (x,y)\in D\}$ and
--
--   $$f^*(x)=\inf_{y\in D_x}f(x,y).$$
--
--   Then $\operatorname{proj}_X(D)$ is open in $X$, $f^*$ is upper semicontinuous, and for every $\varepsilon>0$ there is a Borel-measurable function $\varphi_\varepsilon:\operatorname{proj}_X(D)\to Y$ with $(x,\varphi_\varepsilon(x))\in D$ for all $x\in\operatorname{proj}_X(D)$ and
--
--   $$f\bigl(x,\varphi_\varepsilon(x)\bigr)\le\begin{cases}f^*(x)+\varepsilon&\text{if }f^*(x)>-\infty,\\[2pt]-1/\varepsilon&\text{if }f^*(x)=-\infty.\end{cases}$$
--
--   In contrast to the lower semicontinuous case (Proposition 7.33), the infimum need not be attained, and the proposition provides a Borel-measurable control that is optimal up to $\varepsilon$, with the bound $-1/\varepsilon$ when the infimum is $-\infty$.
--
--   **Formalization Note** $f$ is a function on all of $X\times Y$ whose values off $D$ play no role; its upper semicontinuity is `UpperSemicontinuousOn f D`, and that of $f^*$ is relative to $\operatorname{proj}_X(D)=$ `Prod.fst '' D`. The two cases of the bound are stated as two implications. When $f^*(x)=+\infty$ the first case holds trivially, as in the book, since $+\infty+\varepsilon=+\infty$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, pp. 154–155, Proposition 7.34 (Eqs. (67)–(68) of Chapter 7)

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Proposition 7.34 (Bertsekas & Shreve, pp. 154–155). Let `X` be metrizable, `Y` separable
metrizable, `D ⊆ X × Y` open, `f : D → R*` upper semicontinuous, and
`f*(x) = inf_{y ∈ D_x} f(x, y)` on `proj_X(D)` (Eq. (67) of Chapter 7). Then `proj_X(D)` is open,
`f*` is upper semicontinuous, and for every `ε > 0` there is a Borel-measurable
`φ_ε : proj_X(D) → Y` with `Gr(φ_ε) ⊆ D` and, for all `x ∈ proj_X(D)`,
`f(x, φ_ε(x)) ≤ f*(x) + ε` if `f*(x) > −∞` and `f(x, φ_ε(x)) ≤ −1/ε` if `f*(x) = −∞`
(Eq. (68)). `f` is given on all of `X × Y`; only its values on `D` matter. -/
theorem prop7_34_usc_epsilon_selector {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [SeparableSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsOpen D) (f : X × Y → EReal) (hf : UpperSemicontinuousOn f D) :
    IsOpen (Prod.fst '' D) ∧
    UpperSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∀ ε : ℝ, 0 < ε → ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) ≠ ⊥ →
          f ((x : X), φ x) ≤ (⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) + (ε : EReal)) ∧
        ((⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y)) = ⊥ →
          f ((x : X), φ x) ≤ ((-1 / ε : ℝ) : EReal)) := by sorry

end BertsekasShreve.SemicontSelection
