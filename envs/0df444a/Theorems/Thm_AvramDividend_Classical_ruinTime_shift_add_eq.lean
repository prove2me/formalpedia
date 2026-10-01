-- Prove2me | Theorems.Thm_AvramDividend_Classical_ruinTime_shift_add_eq
-- name    : AvramDividend.Classical.ruinTime_shift_add_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T09:39:55.740165+00:00
-- url     : https://prove2.me/theorems/55eb16d3-5043-4502-8140-8da040854c59
-- title:
--   Prepending a lump sum leaves the ruin time unchanged when both reserves are nonnegative at zero
-- statement:
--   Let $X$ be a spectrally negative Lévy process and let $E$ be a dividend strategy admissible from initial capital $c$ under the cap $\mathrm{ofReal}\,c$, and put $\delta=x-c$ with $0\le c<x$. Form $F$ by declaring $F_0=0$ and $F_t=\delta+E_t$ for $t>0$. Then the ruin time $\sigma^F_x$ of $F$ started from $x$ equals the ruin time $\sigma^E_c$ of $E$ started from $c$.
--
--   Indeed the controlled reserves coincide at every strictly positive time, because $x+X_t-F_t=c+X_t-E_t$. At time zero the two reserves are $x$ and $c$ respectively, since $X_0=0$ and both paths vanish at the origin; both are non-negative because $0\le c<x$, so the strict ruin condition $U_t<0$ fails on both sides at $t=0$. Since the ruin time is the infimum of the times at which the reserve is negative, taken over all $t\ge0$, the two ruin times agree.
-- source:
--   Avram, Palmowski and Pistorius, On the optimal dividend problem for a spectrally negative Lévy process, arXiv:math/0702893v1, §2 (pp. 2-4), for the definition of the ruin time as the infimum over t >= 0 of the strictly negative controlled reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem ruinTime_shift_add_eq {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ)
    (hc : 0 ≤ c)
    (hcx : c < x)
    (E : ℝ≥0 → Ω → ℝ)
    (hE : IsAdmissibleLe X c (ENNReal.ofReal c) E)
    (ω : Ω) :
    ruinTime X x (fun t ω => if t = 0 then 0 else (x - c) + E t ω) ω
      = ruinTime X c E ω := by sorry

end AvramDividend.Classical
