-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_prop7_33_lsc_minimizing_selector
-- name    : BertsekasShreve.SemicontSelection.prop7_33_lsc_minimizing_selector
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:38.527551+00:00
-- url     : https://prove2.me/theorems/caa51840-130b-4af5-a1eb-b1bd97636d30
-- title:
--   Proposition 7.33 — a Borel-measurable exact minimizing selector for lower semicontinuous costs
-- statement:
--   Let $X$ be a metrizable space, $Y$ a compact metrizable space, $D$ a closed subset of $X\times Y$, and $f:D\to R^*$ lower semicontinuous (with respect to the relative topology of $D$). For $x\in X$ let $D_x=\{y\in Y\mid (x,y)\in D\}$ be the section of $D$ at $x$, and let $\operatorname{proj}_X(D)=\{x\mid D_x\ne\emptyset\}$. Define $f^*:\operatorname{proj}_X(D)\to R^*$ by
--
--   $$f^*(x)=\min_{y\in D_x}f(x,y).$$
--
--   Then:
--
--   1. $\operatorname{proj}_X(D)$ is closed in $X$;
--   2. $f^*$ is lower semicontinuous on $\operatorname{proj}_X(D)$;
--   3. there is a Borel-measurable function $\varphi:\operatorname{proj}_X(D)\to Y$ whose graph lies in $D$, i.e. $(x,\varphi(x))\in D$ for every $x\in\operatorname{proj}_X(D)$, and which attains the minimum:
--
--   $$f\bigl(x,\varphi(x)\bigr)=f^*(x)\qquad\forall x\in\operatorname{proj}_X(D).$$
--
--   In dynamic programming terms, $x$ is the state, $y$ the control, $D$ the set of admissible state–control pairs and $f$ the cost-to-go. The proposition says that when the cost is lower semicontinuous and the controls range over a compact set, the minimum over admissible controls is attained and a minimizing control can be chosen as a Borel-measurable function of the state, which is what makes an optimal Borel-measurable policy possible in the semicontinuous models of Chapters 8 and 9.
--
--   **Formalization Note** $f$ is a function on all of $X\times Y$ whose values off $D$ play no role; its lower semicontinuity is `LowerSemicontinuousOn f D`, which is lower semicontinuity of the restriction to the subspace $D$. $\operatorname{proj}_X(D)$ is the image `Prod.fst '' D`; $f^*$ is written $\inf_{y\in D_x}f(x,y)$ (the minimum is attained, as the third conclusion asserts), and its lower semicontinuity is relative to $\operatorname{proj}_X(D)$. $\varphi$ is defined on the subtype $\operatorname{proj}_X(D)$, which carries the Borel σ-algebra of its subspace topology (the trace of the Borel σ-algebra of $X$).
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 153, Proposition 7.33 (Eqs. (65)–(66) of Chapter 7)

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Proposition 7.33 (Bertsekas & Shreve, p. 153). Let `X` be metrizable, `Y` compact metrizable,
`D ⊆ X × Y` closed, `f : D → R*` lower semicontinuous, and `f*(x) = min_{y ∈ D_x} f(x, y)` on
`proj_X(D)` (Eq. (65) of Chapter 7). Then `proj_X(D)` is closed, `f*` is lower semicontinuous,
and there is a Borel-measurable `φ : proj_X(D) → Y` with `Gr(φ) ⊆ D` and
`f(x, φ(x)) = f*(x)` for all `x ∈ proj_X(D)` (Eq. (66)). `f` is given on all of `X × Y`; only its
values on `D` matter, and lower semicontinuity is relative to `D`. -/
theorem prop7_33_lsc_minimizing_selector {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MetrizableSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (D : Set (X × Y)) (hD : IsClosed D) (f : X × Y → EReal) (hf : LowerSemicontinuousOn f D) :
    IsClosed (Prod.fst '' D) ∧
    LowerSemicontinuousOn (fun x => ⨅ (y : Y) (_ : (x, y) ∈ D), f (x, y)) (Prod.fst '' D) ∧
    ∃ φ : (Prod.fst '' D) → Y, Measurable φ ∧
      ∀ x : (Prod.fst '' D), ((x : X), φ x) ∈ D ∧
        f ((x : X), φ x) = ⨅ (y : Y) (_ : ((x : X), y) ∈ D), f ((x : X), y) := by sorry

end BertsekasShreve.SemicontSelection
