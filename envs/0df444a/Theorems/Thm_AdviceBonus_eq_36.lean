-- Prove2me | Theorems.Thm_AdviceBonus_eq_36
-- name    : AdviceBonus.eq_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:06.190303+00:00
-- url     : https://prove2.me/theorems/2504774b-fa1a-4d30-9640-f96d2771fe56
-- title:
--   Proof of the transformation in (36) — the derivatives of $\Pr(1)$ and $\Pr_n(2)$ at a symmetric scheme, (36) and (37)
-- statement:
--   Let the posterior distribution satisfy the standing assumptions, let $w>0$, and consider the symmetric compensation $(f,b)$ for both firms with $0<b<w$. Write $\bar q^A_2$ for the cutoff (2) at this profile. Then the partial derivatives of the sales probabilities with respect to firm $A$'s own commission and bonus are
--   $$
--   \Pr{}^f(1)=0,\qquad \Pr{}^b(1)=-\frac{g(\bar q^A_2)}{4w},
--   $$
--   $$
--   \Pr{}^f_A(2)=\frac{4g(1/2)[1-G(\bar q^A_2)]^2+g(\bar q^A_2)}{4w}\quad(37),\qquad \Pr{}^b_A(2)=\frac{2g(1/2)[1-G(\bar q^A_2)]^2+g(\bar q^A_2)}{4w},
--   $$
--   the derivatives of $\Pr(1)$ and $\Pr_B(2)$ with respect to firm $B$'s own commission and bonus take the same four values, and consequently
--   $$
--   2\Pr{}^b_n(2)-\Pr{}^f_n(2)=\frac{g(\bar q^A_2)}{4w}. \qquad(36)
--   $$
--
--   These are the derivative values that turn the first-order conditions (35) and (7) into the closed forms (14) and (16).
--
--   Differences from the source:
--   - reading: q̄1 by (4), no corner convention → clamped to [0, 1]; reason: the convention of footnote 19 for (2) and (3); at the symmetric scheme q̄1 = 1/2 is interior
--   - reading: density g > 0 on [0, 1], hazard rate increasing on [0, 1] → g continuous and positive on [0, 1], hazard rate weakly increasing on [0, 1); reason: the proofs use continuity (intermediate value theorem, p.35) and the hazard rate is undefined at q = 1
-- source:
--   Honda–Inderst–Ottaviani, When Liability is Not Enough, SSRN 4125013 (May 2022), Appendix A, eq. (36) and the proof of the transformation in (36), pp.34–35, with eq. (37), p.35

import Mathlib
import Definitions.Def_AdviceBonus_Model

namespace AdviceBonus

/-- **Proof of the transformation in (36)**, Appendix A, pp.34–35, with (37), p.35
(Honda–Inderst–Ottaviani, SSRN 4125013, May 2022). At a symmetric scheme `(f, b)` with
`0 < b < w`, write `q̄^A_2` for the cutoff (2) there. The partial derivatives of the sales
probabilities in firm A's own instruments are
`Pr^f(1) = 0`, `Pr^b(1) = −g(q̄^A_2)/(4w)`,
`Pr^f_A(2) = (4g(1/2)[1 − G(q̄^A_2)]² + g(q̄^A_2))/(4w)` (37),
`Pr^b_A(2) = (2g(1/2)[1 − G(q̄^A_2)]² + g(q̄^A_2))/(4w)`, the same values hold for firm B's own
instruments with `Pr_B(2)` (p.35), and hence (36): `2Pr^b_n(2) − Pr^f_n(2) = g(q̄^A_2)/(4w)`. -/
theorem eq_36 (D : Dist) (w : ℝ) (hw : 0 < w) (f b : ℝ) (hb : 0 < b) (hbw : b < w) :
    let a := q2A w (f, b) (f, b)
    let dPr2f := (4 * D.g (1 / 2) * (1 - D.G a) ^ 2 + D.g a) / (4 * w)
    let dPr2b := (2 * D.g (1 / 2) * (1 - D.G a) ^ 2 + D.g a) / (4 * w)
    HasDerivAt (fun x => pr1 D w (x, b) (f, b)) 0 f ∧
    HasDerivAt (fun y => pr1 D w (f, y) (f, b)) (-(D.g a / (4 * w))) b ∧
    HasDerivAt (fun x => prA2 D w (x, b) (f, b)) dPr2f f ∧
    HasDerivAt (fun y => prA2 D w (f, y) (f, b)) dPr2b b ∧
    HasDerivAt (fun x => pr1 D w (f, b) (x, b)) 0 f ∧
    HasDerivAt (fun y => pr1 D w (f, b) (f, y)) (-(D.g a / (4 * w))) b ∧
    HasDerivAt (fun x => prB2 D w (f, b) (x, b)) dPr2f f ∧
    HasDerivAt (fun y => prB2 D w (f, b) (f, y)) dPr2b b ∧
    2 * dPr2b - dPr2f = D.g a / (4 * w) := by sorry

end AdviceBonus
