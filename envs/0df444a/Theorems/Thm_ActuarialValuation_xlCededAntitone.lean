-- Prove2me | Theorems.Thm_ActuarialValuation_xlCededAntitone
-- name    : ActuarialValuation.xlCededAntitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T09:01:40.940191+00:00
-- url     : https://prove2.me/theorems/79010d48-57d9-40d7-bc94-809758f62a3e
-- title:
--   Ceded loss falls as retention rises
-- statement:
--   Raising the insurer's retention cannot increase the amount transferred to the reinsurer.
--
--   **Mathematical statement**
--
--   $$
--   a\le b\Rightarrow c(z,b)\le c(z,a)
--   $$
-- source:
--   Bäuerle and Glauner (2021), Minimizing spectral risk measures applied to Markov decision processes, Section 6 Dynamic optimal reinsurance, https://doi.org/10.1007/s00186-021-00746-w, expected premium principle pi_R(X)=(1+theta)E[X]; Glauner (2022), Dynamic reinsurance in discrete time minimizing the insurer's cost of capital, Scandinavian Actuarial Journal https://doi.org/10.1080/03461238.2021.1964590; Brachetta Ceci (2019), Optimal Excess-of-Loss Reinsurance for Stochastic Factor Risk Models, https://doi.org/10.3390/risks7020048

import Mathlib
import Definitions.Def_actuarial_xlCededLoss
open MeasureTheory

namespace ActuarialValuation

theorem xlCededAntitone (z a b : ℝ) (hab : a ≤ b)
  :
  xlCededLoss z b ≤ xlCededLoss z a := by sorry

end ActuarialValuation
