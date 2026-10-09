-- Prove2me | Theorems.Thm_ActuarialValuation_termAssurancePV_eq_sum
-- name    : ActuarialValuation.termAssurancePV_eq_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T18:14:36.405876+00:00
-- url     : https://prove2.me/theorems/5954d686-5661-4f3b-bfab-191a7d7ddd6d
-- title:
--   Term-assurance present value is a death-year sum
-- statement:
--   Show that the present value is the sum of possible discounted end-of-year death payments, including year n and excluding year n+1.
--
--   **Mathematical statement**
--
--   $$
--   Z_n(\omega)=\sum_{k=0}^{n-1}v^{k+1}\mathbf1_{D_k}(\omega)
--   $$
-- source:
--   Chapter 3 §3.2.2, equation (3.8), https://openacttextdev.github.io/LifeCon/C-SimpleBenefit.html.

import Mathlib
import Definitions.Def_actuarial_deathYearEvent
import Definitions.Def_actuarial_termAssurancePV
open MeasureTheory

namespace ActuarialValuation
theorem termAssurancePV_eq_sum {Ω : Type*}
    (K : Ω → ℕ) (v : ℝ) (n : ℕ) (ω : Ω)
    :
    termAssurancePV K v n ω =
      ∑ k ∈ Finset.range n, v ^ (k + 1) *
        (deathYearEvent K k).indicator (fun _ : Ω => (1 : ℝ)) ω := by sorry
end ActuarialValuation
