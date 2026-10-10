-- Prove2me | Theorems.Thm_ActuarialValuation_clClaimsDevelopment_fundamental
-- name    : ActuarialValuation.clClaimsDevelopment_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T07:51:55.457134+00:00
-- url     : https://prove2.me/theorems/7925d79b-f517-483c-8032-49047bcc0552
-- title:
--   Prior expected ultimate and Bornhuetter-Ferguson reconciliation: clClaimsDevelopment_fundamental
-- statement:
--   The substantive capstone reconciles a volume-selected development factor, chain-ladder valuation, and prior-informed Bornhuetter-Ferguson valuation under economically meaningful positivity assumptions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   fD=N,\;C+R_{CL}=U_{CL},\;U_{BF}=wU_{CL}+(1-w)E,\;R_{CL},R_{BF}\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 283. Klaus D. Schmidt, Methods and Models of Loss Reserving Based on Run-Off Triangles, Casualty Actuarial Society Forum (2006), https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf; Casualty Actuarial Society, The Bornhuetter-Ferguson Principle (2008), https://www.casact.org/sites/default/files/2021-07/Bornhuetter-Ferguson-Schmidt-Zocher.pdf. Parent topic: Finite cumulative claim triangles, volume-weighted age-to-age factors, development-to-ultimate and Bornhuetter-Ferguson reserve valuation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.casact.org/sites/default/files/database/forum_06fforum_273.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator
import Definitions.Def_actuarial_clVolumeFactor
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clReserve
import Definitions.Def_actuarial_clPaidFraction
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFReserve
import Definitions.Def_actuarial_clBFUltimate

namespace ActuarialValuation

theorem clClaimsDevelopment_fundamental (paid : ℕ → ℕ → ℝ) (m j : ℕ) (hD : clLinkDenominator paid m j ≠ 0) (latest prior : ℝ) (factor : ℝ) (hF : 1 ≤ factor) (hC : 0 ≤ latest) (hE : 0 ≤ prior) : (clVolumeFactor paid m j * clLinkDenominator paid m j = clLinkNumerator paid m j) ∧ (latest + clReserve latest factor = clUltimate latest factor) ∧ (clBFUltimate latest prior factor = clPaidFraction factor * clUltimate latest factor + clUnpaidFraction factor * prior) ∧ (0 ≤ clReserve latest factor) ∧ (0 ≤ clBFReserve prior factor) := by sorry

end ActuarialValuation
