-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendValue_add_initial_lump
-- name    : AvramDividend.Classical.dividendValue_add_initial_lump
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T08:37:41.879301+00:00
-- url     : https://prove2.me/theorems/a0df7aaf-ff51-4f95-a128-a030e600e3b5
-- title:
--   Prepending a deterministic lump sum at time zero adds its amount to the discounted dividend value
-- statement:
--   Let $X$ be a spectrally negative Lévy process and let $E$ be a dividend strategy admissible from initial capital $c$ under the cap $C=\mathrm{ofReal}\,c$. Write $\delta=x-c>0$ and form the strategy $F$ by declaring $F_0=0$ and $F_t=\delta+E_t$ for every $t>0$: that is, $F$ pays the compulsory lump sum $\delta$ immediately at time zero (recorded as $F_0=0$ with a jump of size $F_{0+}$ at time $0$) and thereafter follows $E$.
--
--   Then the discounted dividend value of $F$ started from $x$ is exactly $\delta$ plus the discounted dividend value of $E$ started from $c$, where values are taken in $[0,\infty]$.
--
--   The proof has three ingredients. First, the controlled reserve processes agree at strictly positive times, since $x+X_t-F_t=c+X_t-E_t$; at time zero they are $x$ and $c$, and both are non-negative because $0\le c<x$, so neither satisfies the strict ruin condition and the two ruin times coincide. Second, the Lebesgue--Stieltjes measure $dF$ of the shifted path satisfies $dF=\delta\,\delta_0+dE$, with $\delta_0$ the unit atom at the origin: the dividend measure is built from the right-limit version of the path, extended by $0$ on $(-\infty,0)$, and its atom at the origin is therefore $F_{0+}-0=\delta+E_{0+}$, which is the atom of $dE$ at the origin plus $\delta$. Third, the payment times contain the origin unconditionally, and $e^{-q\cdot 0}=1$, so the extra atom contributes precisely $\mathrm{ofReal}\,\delta$ to the discounted integral. All arithmetic is in $\mathbb{R}_{\ge0\infty}$, where no cancellation is used.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, §3.3 (p. 7), for the barrier/lump-sum structure of the admissible class Π; the value identity is the elementary observation that a deterministic payment at time zero is discounted by e^0 = 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem dividendValue_add_initial_lump {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x c : ℝ)
    (hc : 0 ≤ c) (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (hE : IsAdmissibleLe X c (ENNReal.ofReal c) E) :
    dividendValue X q x
        (fun t ω => if t = 0 then 0 else (x - c) + E t ω) =
      ENNReal.ofReal (x - c) + dividendValue X q c E := by sorry

end AvramDividend.Classical
