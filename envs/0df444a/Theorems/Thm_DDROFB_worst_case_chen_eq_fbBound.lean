-- Prove2me | Theorems.Thm_DDROFB_worst_case_chen_eq_fbBound
-- name    : DDROFB.worst_case_chen_eq_fbBound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:09:17.799988+00:00
-- url     : https://prove2.me/theorems/9f41ea30-450c-4adc-8a8e-ce7e63c8a6d1
-- title:
--   Proof of Theorem 6: (24) is the worst-case value of (22) over $\mathcal P^{FB}$
-- statement:
--   Let $m_b, m_f, \bar\sigma_f, \bar\sigma_b \in \mathbb R^d$ with $m_{bi} \le m_{fi}$, $\bar\sigma_{fi} > 0$ and $\bar\sigma_{bi} > 0$ for every $i$, let $0<\epsilon<1$ and $v \in \mathbb R^d$. Then
--
--   $$
--   \sup_{\mathbb P \in \mathcal P^{FB}} \Bigl[\sum_{i=1}^d \mathbb E^{\mathbb P}[\tilde u_i]\, v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i<0} \sigma_b(\mathbb P_i)^2 v_i^2 + \sum_{i : v_i \ge 0} \sigma_f(\mathbb P_i)^2 v_i^2\Bigr)}\Bigr] \;=\; \sum_{i : v_i \ge 0} m_{fi} v_i + \sum_{i : v_i < 0} m_{bi} v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i \ge 0} \bar\sigma_{fi}^2 v_i^2 + \sum_{i : v_i < 0} \bar\sigma_{bi}^2 v_i^2\Bigr)} ,
--   $$
--
--   where $\mathcal P^{FB}$ is the forward–backward confidence region with thresholds $m_b, m_f, \bar\sigma_f, \bar\sigma_b$: the right-hand side of (24) is the least upper bound of the values of the right-hand side of (22) over $\mathcal P^{FB}$.
--
--   Combined with the bound (22), this is Step 2 of the schema for $\mathcal P^{FB}$: the worst-case Value at Risk over the confidence region is at most (24).
--
--   Differences from the source:
--   - encoding: the worst-case value of (22) over P^FB → IsLUB of {chenBound P ε v : P ∈ PFB} at fbBound; reason: the worst-case value is the supremum; IsLUB states it without Lean's junk value for a real sSup
--   - reading: P^FB = {P : P_i ∈ P^FB_i, i = 1,…,d} (conditions on the marginals only) → PFB also requires independent components (HasIndepComponents P); reason: p. 9 defines the confidence region as the measures consistent with the a priori assumptions of the test, here independent components (Sec. 5.2, Theorem 6); the bound (22) applied in the proof holds only for independent marginals; P∗ is independent, so the coverage event is unchanged
--   - reading: P^FB_i ⊆ Θ(−∞,∞) under the section's standing assumption that P∗ has bounded support → PFB contains measures of unbounded support; reason: Θ(−∞,∞) is the set of all Borel probability measures on ℝ (p. 9); the supremum is the same under either reading, since it is approached by products of two-point (bounded) marginals
--   - encoding: thresholds σ̄_fi, σ̄_bi (divisors in (23)) and m_bi ≤ m_fi → hypotheses 0 < σf i, 0 < σb i and mb i ≤ mf i; reason: σ̄ = 0 divides by zero in (23), where Lean's y²/0 = 0 would silently drop the constraint; m_b > m_f makes (23) empty and (24) meaningless
--   - encoding: level ϵ → hypotheses 0 < ε and ε < 1; reason: the schema's range 0 < ϵ < 1 (p. 10); for ε ≥ 1, log(1/ε) ≤ 0 and the square root in the formula is not defined
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, proof of Theorem 6, p. ec5 = PDF p. 43 (unnumbered: "By inspection, (24) is the worst-case value of (22) over P^FB")

import Mathlib
import Definitions.Def_DDROFB_PFB
import Definitions.Def_DDROFB_chenBound
import Definitions.Def_DDROFB_fbBound
open MeasureTheory

namespace DDROFB

/-- **(24) is the worst-case value of (22) over `P^FB`.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, proof of Theorem 6,
p. ec5 = PDF p. 43 (unnumbered): "By inspection, (24) is the worst-case value of (22) over
`P^FB`."

For thresholds `mb ≤ mf`, `σf, σb > 0`, every `0 < ε < 1` and every direction `v`, the supremum of
the right-hand side of (22) over the measures `P ∈ P^FB` equals the right-hand side of (24).

**Formalization Note.** "The worst-case value" is the supremum, stated as `IsLUB` of the image of
`P^FB` under `P ↦ chenBound P ε v`; both halves are asserted (the bound and its sharpness). `P^FB`
contains only measures with independent components (see `PFB`). The positivity of the
thresholds and `mb ≤ mf` are the same encodings as in (23)–(24). -/
theorem worst_case_chen_eq_fbBound {d : ℕ} (mb mf σf σb : Fin d → ℝ) (hm : ∀ i, mb i ≤ mf i)
    (hσf : ∀ i, 0 < σf i) (hσb : ∀ i, 0 < σb i) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (v : EuclideanSpace ℝ (Fin d)) :
    IsLUB ((fun P => chenBound P ε v) '' PFB mb mf σf σb) (fbBound mb mf σf σb ε v) := by sorry

end DDROFB
