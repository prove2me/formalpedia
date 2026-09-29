-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_LinkedODE_offer_cdf_eq_value_cdf
-- name    : ChatterjeeSamuelson.LinkedODE.offer_cdf_eq_value_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:46:32.204291+00:00
-- url     : https://prove2.me/theorems/b80382cd-ecd7-4ad2-a715-3ef881d21d61
-- title:
--   Proof of Theorem 2: $G_b(S(y)) = F_b(y)$
-- statement:
--   Let the buyer's belief $\mu_b$ about the seller's value be a regular belief on $[\underline v_s, \bar v_s]$ with distribution function $F_b$, and let the seller's offer strategy $S$ be of class $A$ on $[\underline v_s, \bar v_s]$. Let $y$ lie in an open interval $(a, c) \subseteq [\underline v_s, \bar v_s]$ on which $S$ is strictly increasing. Then the buyer's probability that the seller offers at most $S(y)$ equals the probability that the seller's value is at most $y$:
--
--   $$
--   G_b(S(y)) := \mu_b\{v_s : S(v_s) \le S(y)\} = F_b(y).
--   $$
--
--   This is the identity $G_b(b) = F_b(S^{-1}(b))$ used in the proof of Theorem 2 to translate the distribution of seller offers into the distribution of seller values.
-- source:
--   Chatterjee & Samuelson, Bargaining under Incomplete Information, Oper. Res. 31(5) (1983), p. 840 [PDF 6], proof of Theorem 2, display "G_b(b) = F_b(S⁻¹(b))"

import Mathlib
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_RegularBelief
import Definitions.Def_ChatterjeeSamuelson_LinkedODE_ClassA

open MeasureTheory ProbabilityTheory Set

namespace ChatterjeeSamuelson.LinkedODE

/-- The distribution of seller offers at an offer `S(y)` (Chatterjee & Samuelson,
*Bargaining under Incomplete Information*, Oper. Res. 31(5) 1983, §2, p. 840 [PDF 6],
proof of Theorem 2, unnumbered display "G_b(b) = F_b(S⁻¹(b)) … Equivalently,
G_b(b) = F_b(y), where y is a dummy variable defined so that b = S(y)").

Let the buyer's belief `μb` about the seller's value be regular on `[loS, hiS]`, let the
seller's strategy `S` be of class `A` on `[loS, hiS]`, and let `y` lie in an open interval
`(a, c) ⊆ [loS, hiS]` on which `S` is strictly increasing. Then the buyer's probability that
the seller offers at most `S(y)`, i.e. `G_b(S(y))`, equals `F_b(y) = cdf μb y`.

*Formalization Note.* `G_b(b)` is `μb {v_s | S v_s ≤ b}` (the law of the seller's offer
under the buyer's belief); `S⁻¹(b)` is the value `y` with `S y = b`, taken as a bound
variable rather than an inverse function. -/
theorem offer_cdf_eq_value_cdf (μb : Measure ℝ) (loS hiS : ℝ) (fb S : ℝ → ℝ)
    (hμb : RegularBelief μb loS hiS fb) (hS : ClassA S loS hiS)
    (a c y : ℝ) (ha : loS ≤ a) (hc : c ≤ hiS) (hy : y ∈ Ioo a c)
    (hmono : StrictMonoOn S (Ioo a c)) :
    (μb {vs | S vs ≤ S y}).toReal = cdf μb y := by sorry

end ChatterjeeSamuelson.LinkedODE
