-- Prove2me | Theorems.Thm_DualSSD_Duality_pQuantile_set_eq_Icc
-- name    : DualSSD.Duality.pQuantile_set_eq_Icc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:36:53.231948+00:00
-- url     : https://prove2.me/theorems/1b953710-b0fd-428e-b6bb-a554a4ade743
-- title:
--   §3, p. 64 — the $p$-quantiles form a closed interval with left end $F_X^{(-1)}(p)$
-- statement:
--   Let $X$ be a random variable and $p\in(0,1)$. Call $q$ a $p$-quantile of $X$ if $\mathbb P\{X<q\}\le p\le\mathbb P\{X\le q\}$. Then there is $b\ge F_X^{(-1)}(p)$ such that
--   $$\{q\in\mathbb R:\ q\text{ is a }p\text{-quantile of }X\}=\big[F_X^{(-1)}(p),\,b\big],$$
--   where $F_X^{(-1)}(p)=\inf\{\eta: \mathbb P\{X\le\eta\}\ge p\}$.
--
--   The left quantile $F_X^{(-1)}(p)$ is thus always a $p$-quantile, which is how the paper chooses the maximizer of the conjugate in the proof of Theorem 3.1.
--
--   **Formalization Note** Only (almost-everywhere) measurability of $X$ is assumed; no moment condition is needed.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 64, last sentence of the page (cited to [4])

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile

namespace DualSSD.Duality

open MeasureTheory

/-- Ogryczak–Ruszczyński 2002, §3, p. 64 (last sentence): for `p ∈ (0, 1)` the set of
`p`-quantiles of `X` (the `q` with `P{X < q} ≤ p ≤ P{X ≤ q}`) is a closed interval whose left
end is `F_X^(−1)(p)`. Only measurability of `X` is assumed. -/
theorem pQuantile_set_eq_Icc {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : AEMeasurable X P)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ b : ℝ, leftQuantile P X p ≤ b ∧
      {q : ℝ | IsPQuantile P X p q} = Set.Icc (leftQuantile P X p) b := by sorry

end DualSSD.Duality
