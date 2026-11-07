-- Prove2me | Theorems.Thm_CutwidthCircuitLB_appendix_A_cubic_cutwidth
-- name    : CutwidthCircuitLB.appendix_A_cubic_cutwidth
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:49.471245+00:00
-- url     : https://prove2.me/theorems/4abd618c-413a-4e5c-af04-f3a379df0574
-- title:
--   Appendix A — $\mathrm{cw}(H) \le (\kappa_E + \xi)h + C_\xi$ for simple 3-regular $H$
-- statement:
--   For every $\xi > 0$ there is a constant $C_\xi$ such that every simple 3-regular graph $H$ on $h$ vertices satisfies
--   $$
--   \mathrm{cw}(H) \le (\kappa_E + \xi)\, h + C_\xi ,\qquad \kappa_E = \frac{3}{2\pi}\arccos\frac{1+2\sqrt2}{4}.
--   $$
--
--   This is the upshot of the Gaussian edge-score argument of Appendix A; since the kernel has $h \le 2(M - N)$ vertices, it proves Theorem 4.6.
--
--   Differences from the source: none.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Appendix A, p.21

import Mathlib
import Definitions.Def_CutwidthCircuitLB_cutSize
import Definitions.Def_CutwidthCircuitLB_CutwidthLE
import Definitions.Def_CutwidthCircuitLB_kappaE

namespace CutwidthCircuitLB

/-- **Appendix A, cutwidth of simple 3-regular graphs** (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Appendix A, p.21): for every `ξ > 0`
there is a constant `C_ξ` such that every simple 3-regular graph `H` on `h` vertices has
`cw(H) ≤ (κ_E + ξ)h + C_ξ`. -/
theorem appendix_A_cubic_cutwidth (ξ : ℝ) (hξ : 0 < ξ) :
    ∃ Cξ : ℝ, ∀ (h : ℕ) (H : SimpleGraph (Fin h)) [DecidableRel H.Adj],
      H.IsRegularOfDegree 3 → CutwidthLE H.edgeFinset.val ((kappaE + ξ) * h + Cξ) := by sorry

end CutwidthCircuitLB
