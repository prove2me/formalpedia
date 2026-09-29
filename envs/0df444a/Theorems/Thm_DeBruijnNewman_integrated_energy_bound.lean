-- Prove2me | Theorems.Thm_DeBruijnNewman_integrated_energy_bound
-- name    : DeBruijnNewman.integrated_energy_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:40:48.834711+00:00
-- url     : https://prove2.me/theorems/dac74a82-d1a1-4a25-b054-7e8af8cfc41a
-- title:
--   Theorem 17 - the time-integrated renormalized energy is $o(T\log^3 T)$
-- statement:
--   Theorem 17, equation (65), under the standing assumption $\Lambda < 0$. Let $x$ assign to each time $t$ with $\Lambda < t \le 0$ an enumeration of the zeros of $H_t$, let $(\xi_j)$ be classical locations, and let $\varepsilon > 0$. Then there is $T_0 > 0$ such that for every $T \ge T_0$ the renormalized energy of the block of indices $[\tfrac12 T\log T,\, 3T\log T]$,
--   $$\tilde E_I(t) = \sum_{j,k \in I,\ j \ne k} \frac{1}{|\xi_k - \xi_j|^2}\,V\!\left(\frac{x_k(t) - x_j(t)}{\xi_k - \xi_j}\right), \qquad I = [\lceil \tfrac12 T\log T\rceil,\ \lfloor 3T\log T\rfloor]_{\mathbb{Z}^*},$$
--   is absolutely integrable in $t$ over $(\Lambda/4, 0]$ and
--   $$\left|\int_{\Lambda/4}^{0} \tilde E_I(t)\,dt\right| \le \varepsilon\, T (\log_+ T)^3 .$$
--   Absolute integrability is part of the conclusion, so the bound cannot be met by the convention that a non-integrable function has integral zero. The endpoints of the index block are the integer ceiling and floor of $\tfrac12 T\log T$ and $3T\log T$.
-- source:
--   B. Rodgers and T. Tao, "The de Bruijn-Newman constant is non-negative", Forum of Mathematics, Pi 8 (2020), e6, https://doi.org/10.1017/fmp.2020.6, Theorem 17, equation (65), p. 42

import Mathlib
import Definitions.Def_DeBruijnNewman_core
import Definitions.Def_DeBruijnNewman_zeros
import Definitions.Def_DeBruijnNewman_energy
open MeasureTheory

open MeasureTheory

namespace DeBruijnNewman

theorem integrated_energy_bound (hLambda : Lambda < 0) (x : ℝ → ℤ → ℝ) (xi : ℤ → ℝ)
    (hx : ∀ t : ℝ, Lambda < t → t ≤ 0 → IsZeroEnumeration t (x t))
    (hxi : IsClassicalLocations xi) (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      IntegrableOn (fun t : ℝ => EtildeFinset (x t) xi
          (discreteIcc ⌈0.5 * T * Real.log T⌉ ⌊3 * T * Real.log T⌋)) (Set.Ioc (Lambda / 4) 0) ∧
      |∫ t in Set.Ioc (Lambda / 4) 0, EtildeFinset (x t) xi
          (discreteIcc ⌈0.5 * T * Real.log T⌉ ⌊3 * T * Real.log T⌋)|
        ≤ ε * T * logPlus T ^ 3 := by sorry

end DeBruijnNewman
