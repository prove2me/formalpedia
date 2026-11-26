-- Prove2me | Theorems.Thm_ErdosDyadic_measure_C_le
-- name    : ErdosDyadic.measure_C_le
-- status  : Proved
-- author  : @Jhon Lenin Acuna
-- created : 2026-11-25T04:41:28.933712+00:00
-- url     : https://prove2.me/theorems/5c814334-64b0-4253-bfac-ef2da5645462
-- title:
--   Measure of $C\cap[0,1]$ is at most $\eta/2$
-- statement:
--   Let $\eta\in(0,1)$ and let $(H_j)_{j\ge1}$ be measurable 1-periodic sets with $\rho(H_j)\le 6p_j$, where $p_j=\frac{\eta}{24}2^{-j}$. With $C=\bigcup_{j\ge1}\bigl(2^{-j}H_j\cup(-2^{-j}H_j)\bigr)$,
--   $$m\bigl(C\cap[0,1]\bigr)\le \frac{\eta}{2}.$$
--
--   This is the measure budget in Section 6: the identities $m((\pm2^{-j}H_j)\cap[0,1])=\rho(H_j)$ and countable subadditivity give $m(C\cap[0,1])\le 12\sum_j p_j=\eta/2$.
--
--   **Formalization Note** Periodicity and measurability are assumed for every index $j$ (including $j=0$, which does not enter $C$).
-- source:
--   OpenAI, The dyadic case of the Erdős similarity conjecture, Sept 25, 2026, https://github.com/openai/math/tree/main/preprints/The-dyadic-case-of-the-Erdos-similarity-conjecture-September-25-2026, Section 6, p. 15 (estimate on m(C ∩ [0,1]))

import Mathlib
import Definitions.Def_erdos_dyadic_IsPeriodic1
import Definitions.Def_erdos_dyadic_rho

open MeasureTheory Set

namespace ErdosDyadic

/-- Measure estimate: m(C ∩ [0,1]) ≤ η/2. -/
theorem measure_C_le (η : ℝ) (hη : η ∈ Ioo (0 : ℝ) 1) (H : ℕ → Set ℝ)
    (hper : ∀ j, IsPeriodic1 (H j)) (hmeas : ∀ j, MeasurableSet (H j))
    (hrho : ∀ j, 1 ≤ j → rho (H j) ≤ ENNReal.ofReal (6 * (η / 24 * (1 / 2) ^ j))) :
    volume ((⋃ j ∈ {j : ℕ | 1 ≤ j},
          (((fun y : ℝ => (2 : ℝ) ^ (-(j : ℤ)) * y) '' H j) ∪
           ((fun y : ℝ => -((2 : ℝ) ^ (-(j : ℤ)) * y)) '' H j))) ∩ Icc 0 1)
      ≤ ENNReal.ofReal (η / 2) := by
  sorry

end ErdosDyadic
