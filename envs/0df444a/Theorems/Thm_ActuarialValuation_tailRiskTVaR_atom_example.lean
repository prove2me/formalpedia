-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskTVaR_atom_example
-- name    : ActuarialValuation.tailRiskTVaR_atom_example
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:28:28.059086+00:00
-- url     : https://prove2.me/theorems/49398b9e-c238-4016-95a7-5adc2424cdd8
-- title:
--   Two-coin discrete atom requires fractional quantile allocation
-- statement:
--   A discrete loss with probabilities one-quarter at zero, one-half at one and one-quarter at two has median one. The worst half consists of all loss-two outcomes and half the loss-one atom. Its TVaR is three-halves, unlike conditioning on losses strictly greater than one or at least one.
--
--   **Mathematical statement**
--
--   $$
--   w=(1/4,1/2,1/4),\ \alpha=1/2:\ \operatorname{TVaR}=3/2
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskTVaR_atom_example :
  tailRiskTVaR
    (fun s : ℕ => if s = 0 then (1 / 4 : ℝ) else
      if s = 1 then (1 / 2 : ℝ) else
        if s = 2 then (1 / 4 : ℝ) else 0)
    2 1 (1 / 2) = (3 / 2 : ℝ) := by sorry

end ActuarialValuation
