-- Prove2me | Theorems.Thm_AMPUniversality_Polytope_footnote_3
-- name    : AMPUniversality.Polytope.footnote_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:29.978715+00:00
-- url     : https://prove2.me/theorems/500606d8-b46d-492b-8bd6-19bb3fa2bf12
-- title:
--   Footnote 3, p. 5 — the sampling-ratio curve has a unique positive parameter
-- statement:
--   The sampling coordinate $f_\delta$ of equations (1.2)–(1.3) is strictly decreasing on $[0,\infty)$, begins at one, and tends to zero:
--
--   $$f_\delta(0)=1,\qquad\lim_{\alpha\to\infty}f_\delta(\alpha)=0.$$
--
--   Consequently, every $\delta\in(0,1)$ has exactly one parameter $\alpha>0$ with $f_\delta(\alpha)=\delta$. This ensures that the parameterized goal theorem covers every interior sampling ratio.
-- source:
--   Bayati, Lelarge and Montanari, Universality in polytope phase transitions and message passing algorithms, arXiv:1207.7321v2, p. 5, footnote 3

import Mathlib
import Definitions.Def_AMPUniversality_Polytope_Curve

set_option autoImplicit false
open Filter Set
open scoped Topology

namespace AMPUniversality.Polytope

/-- Footnote 3, p. 5: the parametric sampling curve has a unique positive
parameter at each interior sampling ratio. -/
theorem footnote_3 :
    StrictAntiOn fδ (Ici 0) ∧ fδ 0 = 1 ∧
      Tendsto fδ atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∃! α : ℝ, 0 < α ∧ fδ α = δ := by sorry

end AMPUniversality.Polytope
