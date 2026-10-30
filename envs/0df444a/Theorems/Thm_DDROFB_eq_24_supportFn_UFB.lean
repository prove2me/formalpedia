-- Prove2me | Theorems.Thm_DDROFB_eq_24_supportFn_UFB
-- name    : DDROFB.eq_24_supportFn_UFB
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:08:39.579973+00:00
-- url     : https://prove2.me/theorems/981f2d4b-3585-4048-a5b4-6d9fab97e7d8
-- title:
--   Eq. (24): the support function of $\mathcal U^{FB}_\epsilon$
-- statement:
--   Let $m_b, m_f, \bar\sigma_f, \bar\sigma_b \in \mathbb R^d$ with $m_{bi} \le m_{fi}$, $\bar\sigma_{fi} > 0$ and $\bar\sigma_{bi} > 0$ for every $i$, and let $0<\epsilon<1$. For every $v \in \mathbb R^d$ the support function of the set $\mathcal U^{FB}_\epsilon$ of (23) is
--
--   $$
--   \delta^*(v \mid \mathcal U^{FB}_\epsilon) \;=\; \sum_{i : v_i \ge 0} m_{fi} v_i + \sum_{i : v_i < 0} m_{bi} v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i \ge 0} \bar\sigma_{fi}^2 v_i^2 + \sum_{i : v_i < 0} \bar\sigma_{bi}^2 v_i^2\Bigr)} ,
--   $$
--
--   that is, the right-hand side is the least upper bound of $\{v^\top u : u \in \mathcal U^{FB}_\epsilon\}$.
--
--   This is the second clause of Theorem 6. It shows that the robust constraint $v^\top u \le t$ for all $u \in \mathcal U^{FB}_\epsilon$ is a second-order cone constraint.
--
--   Differences from the source:
--   - encoding: thresholds σ̄_fi, σ̄_bi (divisors in (23)) and m_bi ≤ m_fi → hypotheses 0 < σf i, 0 < σb i and mb i ≤ mf i; reason: σ̄ = 0 divides by zero in (23), where Lean's y²/0 = 0 would silently drop the constraint; m_b > m_f makes (23) empty and (24) meaningless
--   - encoding: level ϵ → hypotheses 0 < ε and ε < 1; reason: the schema's range 0 < ϵ < 1 (p. 10); for ε ≥ 1, log(1/ε) ≤ 0 and the square root in the formula is not defined
--   - encoding: δ∗(v| U^FB_ϵ) equal to the right-hand side of (24) → IsLUB of {⟪v, u⟫ : u ∈ UFB} at fbBound; reason: the least upper bound of the set is the supremum, without Lean's junk value for a real sSup
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (24), p. 19 (proof p. ec5 = PDF p. 43)

import Mathlib
import Definitions.Def_DDROFB_UFB
import Definitions.Def_DDROFB_fbBound
open InnerProductSpace

namespace DDROFB

/-- **The support function of `U^FB_ε` is (24)** (Theorem 6, second clause).
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, Theorem 6, eq. (24),
p. 19: "Moreover, `δ∗(v| U^FB_ϵ) = Σ_{i:v_i≥0} m_{fi} v_i + Σ_{i:v_i<0} m_{bi} v_i +
√(2 log(1/ϵ) (Σ_{i:v_i≥0} σ̄²_{fi} v²_i + Σ_{i:v_i<0} σ̄²_{bi} v²_i))`." (Proof on p. ec5 = PDF
p. 43.)

**Formalization Note.** `δ∗(v| U)` is stated as the least upper bound (`IsLUB`) of
`{⟪v, u⟫ : u ∈ U^FB_ε}`, which is the supremum without Lean's default value for a real `sSup`.
The thresholds satisfy `mb ≤ mf` and `σf, σb > 0` coordinatewise: `σ̄ = 0` divides by zero in
(23) (in Lean `y²/0 = 0` would drop the constraint), and `mb > mf` makes the set empty. The level
is `0 < ε < 1`. -/
theorem eq_24_supportFn_UFB {d : ℕ} (mb mf σf σb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : EuclideanSpace ℝ (Fin d)) :
    IsLUB ((fun u => ⟪v, u⟫_ℝ) '' UFB mb mf σf σb ε) (fbBound mb mf σf σb ε v) := by sorry

end DDROFB
