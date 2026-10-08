-- Prove2me | Theorems.Thm_BertsekasShreve_SemicontSelection_prop7_32_inf_semicontinuous
-- name    : BertsekasShreve.SemicontSelection.prop7_32_inf_semicontinuous
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:16.784989+00:00
-- url     : https://prove2.me/theorems/cbe39002-3c8c-4c8b-af8a-6dc88e84cbc7
-- title:
--   Proposition 7.32 — partial infima of semicontinuous functions are semicontinuous
-- statement:
--   Let $X$ and $Y$ be metrizable spaces and let $f:X\times Y\to R^*$, where $R^*=[-\infty,\infty]$. Define
--
--   $$f^*(x)=\inf_{y\in Y}f(x,y)\qquad(x\in X).$$
--
--   1. If $f$ is lower semicontinuous and $Y$ is compact, then $f^*$ is lower semicontinuous, and, when $Y$ is nonempty, for every $x\in X$ the infimum is attained: there is $y\in Y$ with $f(x,y)=f^*(x)$.
--   2. If $f$ is upper semicontinuous, then $f^*$ is upper semicontinuous.
--
--   A function $g$ on a metrizable space is lower semicontinuous if every sublevel set $\{g\le c\}$, $c\in\mathbb R$, is closed, and upper semicontinuous if every superlevel set $\{g\ge c\}$ is closed (Definition 7.13).
--
--   This is the semicontinuity part of the minimization step of the dynamic programming algorithm: it is the first ingredient of the Borel-measurable selection theorem, Proposition 7.33.
--
--   **Formalization Note** Semicontinuity is Mathlib's `LowerSemicontinuous`/`UpperSemicontinuous` for `EReal`-valued functions, which is equivalent to Definition 7.13 (a sublevel set $\{g\le c\}$ for $c\in R^*$ is all of $X$ when $c=+\infty$ and the intersection of the sets $\{g\le -n\}$ when $c=-\infty$). The book asserts attainment for every $x$; for $Y=\emptyset$ the infimum is $+\infty$ and is not attained, so the attainment clause is stated for nonempty $Y$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 148, Proposition 7.32 (Eq. (55) of Chapter 7); Definition 7.13, p. 146

import Mathlib

namespace BertsekasShreve.SemicontSelection

open TopologicalSpace

/-- Proposition 7.32 (Bertsekas & Shreve, p. 148). Let `X`, `Y` be metrizable, `f : X × Y → R*`,
and `f*(x) = inf_{y ∈ Y} f(x, y)` (Eq. (55) of Chapter 7).
(a) If `f` is lower semicontinuous and `Y` is compact, then `f*` is lower semicontinuous and for
every `x` the infimum is attained by some `y ∈ Y` (for nonempty `Y`; when `Y = ∅` the infimum is
`+∞` and nothing attains it).
(b) If `f` is upper semicontinuous, then `f*` is upper semicontinuous. -/
theorem prop7_32_inf_semicontinuous {X Y : Type*}
    [TopologicalSpace X] [MetrizableSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    (f : X × Y → EReal) :
    (LowerSemicontinuous f → CompactSpace Y →
      LowerSemicontinuous (fun x => ⨅ y, f (x, y)) ∧
      ∀ x, Nonempty Y → ∃ y, f (x, y) = ⨅ y', f (x, y')) ∧
    (UpperSemicontinuous f → UpperSemicontinuous (fun x => ⨅ y, f (x, y))) := by sorry

end BertsekasShreve.SemicontSelection
