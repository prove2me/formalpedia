-- Prove2me | Theorems.Thm_FlexLearning_Threshold_aux_poly_bounds
-- name    : FlexLearning.Threshold.aux_poly_bounds
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T11:45:16.102854+00:00
-- url     : https://prove2.me/theorems/58ddfb77-a258-462a-b5ae-93dbe70e76a2
-- title:
--   Auxiliary polynomial inequalities for the proof of Proposition 1 (sign conditions behind ζ ≈ 0.5904)
-- statement:
--   Five explicit one-variable polynomial inequalities used in the algebraic part of the proof of Proposition 1 (threshold $\zeta\approx0.5904$) at $x=0$:
--
--   1. $P_{12}(s)=81s^{12}+972s^{10}-1053s^9-486s^8-648s^7+1314s^6+162s^5-429s^3+54s^2+36s+8>0$ for $0\le s\le 0.578$;
--   2. $P_{20}(s)=-59049s^{20}+78732s^{19}-19683s^{18}+39366s^{17}-65610s^{16}+24057s^{15}+2187s^{14}+4374s^{13}-7290s^{12}-2916s^{11}+3888s^{10}+972s^9-243s^8+162s^7-558s^6+54s^4+24s^3-1>0$ for $\tfrac12\le s\le0.578$;
--   3. $T'(w)=72w^7-504w^6+1176w^5-1185w^4+1044w^3-1116w^2+144w+432>0$ for $0\le w\le1$, where $T(w)=9w^8-72w^7+196w^6-237w^5+261w^4-372w^3+72w^2+432w-288$;
--   4. $9\alpha(w)=3w^7-4w^6-54w^5+117w^4+72w^3-252w^2+144>0$ for $0\le w\le1$;
--   5. $-3\beta(w)=-(4w^5-15w^4-16w^3+60w^2-48)>0$ for $0\le w\le1$.
--
--   **Role in the proof.** With margin $m=(p-c)/p$ and normalised break-even cost: in the regime $2c_F\le p$ (parameter $w=\sqrt{2c_F/p}$, $m^2=1-w^2+w^3/3$) the sign of $V_F-V_N$ equals the sign of $T(w)$, via $\beta^2 m^2-\alpha^2=-w^6T(w)/81$. Items 3–5 give the monotonicity of $T$ and the signs of $\alpha$ and $\beta$. In the regime $2c_F>p$ (parameter $s$ with $m=3s^3$ and $\sqrt{2-2c_F/p}=3s^2$), items 1–2 are the squared forms of $V_F\ge V_N$ for the two possible optimal capacity regimes.
--
--   **Formalization Note.** These are auxiliary inequalities obtained by eliminating square roots in the paper's comparison of $V_F(\tilde c_F)$ and $V_N$. They are not stated in the paper, which reports the threshold numerically.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), Proposition 1 (p. 12) and its proof pp. A3–A8; auxiliary algebraic inequalities arising when the comparison V_F(c̃_F) vs V_N at x = 0 is made exact (not stated in the paper)

import Mathlib

namespace FlexLearning.Threshold

theorem aux_poly_bounds :
    (∀ s : ℝ, (0:ℝ) ≤ s → s ≤ ((289:ℝ)/500) →
      0 < (8:ℝ) + (36:ℝ) * s ^ 1 + (54:ℝ) * s ^ 2 + (-429:ℝ) * s ^ 3 + (162:ℝ) * s ^ 5 + (1314:ℝ) * s ^ 6 + (-648:ℝ) * s ^ 7 + (-486:ℝ) * s ^ 8 + (-1053:ℝ) * s ^ 9 + (972:ℝ) * s ^ 10 + (81:ℝ) * s ^ 12) ∧
    (∀ s : ℝ, ((1:ℝ)/2) ≤ s → s ≤ ((289:ℝ)/500) →
      0 < (-1:ℝ) + (24:ℝ) * s ^ 3 + (54:ℝ) * s ^ 4 + (-558:ℝ) * s ^ 6 + (162:ℝ) * s ^ 7 + (-243:ℝ) * s ^ 8 + (972:ℝ) * s ^ 9 + (3888:ℝ) * s ^ 10 + (-2916:ℝ) * s ^ 11 + (-7290:ℝ) * s ^ 12 + (4374:ℝ) * s ^ 13 + (2187:ℝ) * s ^ 14 + (24057:ℝ) * s ^ 15 + (-65610:ℝ) * s ^ 16 + (39366:ℝ) * s ^ 17 + (-19683:ℝ) * s ^ 18 + (78732:ℝ) * s ^ 19 + (-59049:ℝ) * s ^ 20) ∧
    (∀ w : ℝ, (0:ℝ) ≤ w → w ≤ (1:ℝ) →
      0 < (432:ℝ) + (144:ℝ) * w ^ 1 + (-1116:ℝ) * w ^ 2 + (1044:ℝ) * w ^ 3 + (-1185:ℝ) * w ^ 4 + (1176:ℝ) * w ^ 5 + (-504:ℝ) * w ^ 6 + (72:ℝ) * w ^ 7) ∧
    (∀ w : ℝ, (0:ℝ) ≤ w → w ≤ (1:ℝ) →
      0 < (144:ℝ) + (-252:ℝ) * w ^ 2 + (72:ℝ) * w ^ 3 + (117:ℝ) * w ^ 4 + (-54:ℝ) * w ^ 5 + (-4:ℝ) * w ^ 6 + (3:ℝ) * w ^ 7) ∧
    (∀ w : ℝ, (0:ℝ) ≤ w → w ≤ (1:ℝ) →
      0 < (48:ℝ) + (-60:ℝ) * w ^ 2 + (16:ℝ) * w ^ 3 + (15:ℝ) * w ^ 4 + (-4:ℝ) * w ^ 5) := by sorry

end FlexLearning.Threshold
