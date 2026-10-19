-- Prove2me | Theorems.Thm_ActuarialAnnuities_fractional_guarantee_partition
-- name    : ActuarialAnnuities.fractional_guarantee_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:12:32.375998+00:00
-- url     : https://prove2.me/theorems/04ddfe1c-bee9-43c6-88fa-e5ace324bcd9
-- title:
--   Fractional guarantee partition
-- statement:
--   A micro-frequency guarantee partitions into estate-continuation and post-guarantee survivor payments. The theorem respects the exact payment-date, valuation and guarantee units in the underlying contract.
--
--   Mathematical relation:
--
--   $$
--   V^{(m)}=V^{(m)}_{\text{guarantee}}+V^{(m)}_{\text{post}}
--   $$
--
--   This is an open derived mathematical target, with its complete assumptions recorded in the separate formal proposition.
--
--   Units: Present value in GBP per unit nominal pension, with individual instalments in GBP, payment time in anniversaries and survival as dimensionless probability.
-- source:
--   Original derived finite annuity result. Contextual source page 152, Dickson, Hardy and Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Chapter 5 (and Chapter 4 for assurance). https://api.pageplace.de/preview/DT0400.9781108787406_A49239377/preview-9781108787406_A49239377.pdf. The exact definition or theorem is an original payment-event formalisation, not a numbered published result. A micro-frequency guarantee partitions into estate-continuation and post-guarantee survivor payments.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bUDDMicroMass
import Definitions.Def_actuarial_bFractionalSurvivalPV

namespace ActuarialAnnuities

theorem fractional_guarantee_partition (h a n g delta m : ℕ) (w : ℝ) (b p : ℕ → ℝ) : bFractionalSurvivalPV h a n g delta m w b p = bGuaranteedPV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p) + bPostGuaranteePV (h*m) (a*m) (n*m) g delta w (fun q => b q / (m : ℝ)) (bUDDMicroMass h m p) := by sorry

end ActuarialAnnuities
