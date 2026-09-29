-- Prove2me | Theorems.Thm_DeBruijnNewman_energy_bound_at_time_zero
-- name    : DeBruijnNewman.energy_bound_at_time_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:41:52.864842+00:00
-- url     : https://prove2.me/theorems/3e7804a4-111f-4fbf-a060-43b4a492c993
-- title:
--   Proposition 26 - energy bound at time zero
-- statement:
--   Proposition 26, under the standing assumption $\Lambda < 0$. Let $x$ assign to each time $t$ with $\Lambda < t \le 0$ an enumeration of the zeros of $H_t$, let $(\xi_j)$ be classical locations, and let $\varepsilon > 0$. Then there is $T_0 > 0$ such that for every $T \ge T_0$,
--   $$\tilde E_{[T\log T,\, 2T\log T]}(0) \le \varepsilon\, T (\log T)^3,$$
--   the renormalized energy being taken at time $t = 0$ over the block of nonzero indices between $\lceil T\log T\rceil$ and $\lfloor 2T\log T\rfloor$. This is the quantitative form of the assertion that at time zero the zeros are, on average, in local equilibrium: their gaps agree with the classical spacing $\xi_{j+1} - \xi_j$ apart from a vanishing proportion of exceptions.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Proposition 26, p. 57

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros
import Definitions.Def_DeBruijnNewman_energy

namespace DeBruijnNewman

theorem energy_bound_at_time_zero (hLambda : Lambda < 0) (x : ℝ → ℤ → ℝ) (xi : ℤ → ℝ)
    (hx : ∀ t : ℝ, Lambda < t → t ≤ 0 → IsZeroEnumeration t (x t))
    (hxi : IsClassicalLocations xi) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      EtildeFinset (x 0) xi (discreteIcc ⌈T * Real.log T⌉ ⌊2 * T * Real.log T⌋)
        ≤ ε * T * Real.log T ^ 3 := by sorry

end DeBruijnNewman
