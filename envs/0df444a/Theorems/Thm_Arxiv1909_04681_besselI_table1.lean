-- Prove2me | Theorems.Thm_Arxiv1909_04681_besselI_table1
-- name    : Arxiv1909_04681.besselI_table1
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T06:50:39.554927+00:00
-- url     : https://prove2.me/theorems/80f5e727-1167-4b08-a84c-879ab81fb1e3
-- title:
--   Table 1: $I_4,\dots,I_{10}$ in terms of $I_0, I_1, I_2$
-- statement:
--   Let $I_n$ be the modified Bessel functions of the first kind and let $k>0$. Then, as listed in Table 1,
--
--   $$\begin{aligned}I_4&=\Big(1+\tfrac{24}{k^2}\Big)I_0+\Big(-\tfrac8k-\tfrac{48}{k^3}\Big)I_1,\\ I_5&=\Big(1+\tfrac{48}{k^2}\Big)I_1+\Big(-\tfrac{12}k-\tfrac{192}{k^3}\Big)I_2,\\ I_6&=\Big(1+\tfrac{144}{k^2}+\tfrac{1920}{k^4}\Big)I_0+\Big(-\tfrac{18}k-\tfrac{768}{k^3}-\tfrac{3840}{k^5}\Big)I_1,\\ I_7&=\Big(1+\tfrac{240}{k^2}+\tfrac{5760}{k^4}\Big)I_1+\Big(-\tfrac{24}k-\tfrac{1920}{k^3}-\tfrac{23040}{k^5}\Big)I_2,\\ I_8&=\Big(1+\tfrac{480}{k^2}+\tfrac{28800}{k^4}+\tfrac{322560}{k^6}\Big)I_0+\Big(-\tfrac{32}k-\tfrac{4800}{k^3}-\tfrac{138240}{k^5}-\tfrac{645120}{k^7}\Big)I_1,\\ I_9&=\Big(1+\tfrac{720}{k^2}+\tfrac{67200}{k^4}+\tfrac{1290240}{k^6}\Big)I_1+\Big(-\tfrac{40}k-\tfrac{9600}{k^3}-\tfrac{483840}{k^5}-\tfrac{5160960}{k^7}\Big)I_2,\\ I_{10}&=\Big(1+\tfrac{1200}{k^2}+\tfrac{201600}{k^4}+\tfrac{9031680}{k^6}+\tfrac{92897280}{k^8}\Big)I_0\\&\quad+\Big(-\tfrac{50}k-\tfrac{19200}{k^3}-\tfrac{1693440}{k^5}-\tfrac{41287680}{k^7}-\tfrac{185794560}{k^9}\Big)I_1,\end{aligned}$$
--
--   all Bessel functions evaluated at $k$.
--
--   With $I_0,I_1,I_2$ computed numerically, these give the higher orders needed for the tenth-order mixture distribution.
--
--   **Formalization Note** Table 1 lists, for each $I_n$, the coefficient of each column's Bessel function ($I_0$, $I_1$ or $I_2$); each row is read as that linear combination. The paper presents the rows as approximations obtained by coefficient matching; the statement is the equality, as for eq. (40).
-- source:
--   Christian and Psaltis, Interferometric Closure Phase Uncertainties in the Low Signal-to-Noise Ratio Regime, arXiv:1909.04681v2 (2020), claim c020; Appendix B, Table 1 and the paragraph citing it, PDF pp. 9-10

import Mathlib
import Definitions.Def_Arxiv1909_04681_Basic

open Filter Topology Asymptotics

namespace Arxiv1909_04681

theorem besselI_table1 (k : ℝ) (hk : 0 < k) :
    besselI 4 k = (1 + 24 / k ^ 2) * besselI 0 k + (-8 / k - 48 / k ^ 3) * besselI 1 k ∧
    besselI 5 k = (1 + 48 / k ^ 2) * besselI 1 k + (-12 / k - 192 / k ^ 3) * besselI 2 k ∧
    besselI 6 k = (1 + 144 / k ^ 2 + 1920 / k ^ 4) * besselI 0 k +
      (-18 / k - 768 / k ^ 3 - 3840 / k ^ 5) * besselI 1 k ∧
    besselI 7 k = (1 + 240 / k ^ 2 + 5760 / k ^ 4) * besselI 1 k +
      (-24 / k - 1920 / k ^ 3 - 23040 / k ^ 5) * besselI 2 k ∧
    besselI 8 k = (1 + 480 / k ^ 2 + 28800 / k ^ 4 + 322560 / k ^ 6) * besselI 0 k +
      (-32 / k - 4800 / k ^ 3 - 138240 / k ^ 5 - 645120 / k ^ 7) * besselI 1 k ∧
    besselI 9 k = (1 + 720 / k ^ 2 + 67200 / k ^ 4 + 1290240 / k ^ 6) * besselI 1 k +
      (-40 / k - 9600 / k ^ 3 - 483840 / k ^ 5 - 5160960 / k ^ 7) * besselI 2 k ∧
    besselI 10 k =
      (1 + 1200 / k ^ 2 + 201600 / k ^ 4 + 9031680 / k ^ 6 + 92897280 / k ^ 8) * besselI 0 k +
      (-50 / k - 19200 / k ^ 3 - 1693440 / k ^ 5 - 41287680 / k ^ 7 - 185794560 / k ^ 9) *
        besselI 1 k := by sorry

end Arxiv1909_04681
