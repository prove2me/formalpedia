-- Prove2me | Theorems.Thm_BalkemaDeHaan_DiscreteDomain_tailEquiv_mem_Dr
-- name    : BalkemaDeHaan.DiscreteDomain.tailEquiv_mem_Dr
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:08:27.772979+00:00
-- url     : https://prove2.me/theorems/30475509-af74-4115-9cec-c83383490d9f
-- title:
--   §3, p. 800 — D_r(Π_{p,c}) is closed under tail equivalence
-- statement:
--   Let $p > 0$ and $c \ge 0$, and let $F_1, F_2$ be distribution functions with $F_i(x) < 1$ for all $x$ that are tail equivalent, $1 - F_1(x) \sim 1 - F_2(x)$ as $x \to \infty$. If $F_2 \in D_r(\Pi_{p,c})$, then $F_1 \in D_r(\Pi_{p,c})$.
--
--   Together with the previous milestone this gives the "if" half of Theorem 5.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 800 (PDF 9), §3, sentence before Theorem 5

import Mathlib
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_ResidualLife
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_PiPC
import Definitions.Def_BalkemaDeHaan_DiscreteDomain_DiscreteLaw

open MeasureTheory Filter Topology

namespace BalkemaDeHaan.DiscreteDomain

/-- §3, p. 800 (PDF 9): if `F₁` is BalkemaDeHaan.LimitTypes.tail equivalent to `F₂ ∈ D_r(Π_{p,c})`, then
`F₁ ∈ D_r(Π_{p,c})`. -/
theorem tailEquiv_mem_Dr (p c : ℝ) (hp : 0 < p) (hc : 0 ≤ c)
    (μ₁ μ₂ : Measure ℝ) [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h12 : TailEquiv μ₁ μ₂) (h2 : InDr μ₂ (piPC p c)) :
    InDr μ₁ (piPC p c) := by sorry

end BalkemaDeHaan.DiscreteDomain
