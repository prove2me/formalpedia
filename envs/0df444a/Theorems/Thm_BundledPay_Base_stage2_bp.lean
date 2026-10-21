-- Prove2me | Theorems.Thm_BundledPay_Base_stage2_bp
-- name    : BundledPay.Base.stage2_bp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:54:29.301804+00:00
-- url     : https://prove2.me/theorems/9fd35fb8-6231-476e-8b82-c0f70c89caf9
-- title:
--   Proof of Lemma 5, pp. 34–35 — corrected BP stage-2 responses
-- statement:
--   At a given nonnegative gainsharing amount $T$ below $\Delta c+\Delta r_p$, the base-model bundled-payment effort game has a unique pure Nash equilibrium. Hospital effort is $i_h=1$, and physician effort is the best response clipped to $[0,1]$:
--
--   $$i_p=\max\left\{0,\min\left\{1,\frac{I_0+(\Delta r_p-T)/(2w_b)}{1-\Psi}\right\}\right\}.$$
--
--   This characterizes the continuation game needed to assess the hospital's first-stage gainsharing choice.
--
--   **Formalization Note** The paper's displayed response (39) is garbled. The hospital's monotonicity in effort applies for $T<\Delta c+\Delta r_p$, stated explicitly here.
-- source:
--   Vlachy, Ayer, Ayvaci & Raghunathan, The Business of Healthcare: The Role of Physician Integration in Bundled Payments, SSRN preprint 3539596, pp. 34–35, proof of Lemma 5, stage 2 and eq. (39)

import Mathlib
import Definitions.Def_BundledPay_Base_Model

namespace BundledPay.Base

/-- Corrected stage-2 response in the proof of Lemma 5, pp. 34–35.
The hospital's monotonicity in its effort requires `T < Δc + Δr_p`. -/
theorem stage2_bp (P : Params) (hS : P.Standing) (hwq : P.wq = 0)
    (rBP T ih ip : ℝ) (hT : 0 ≤ T) (hTupper : T < P.dc + P.drp) :
    IsNashBP P rBP T ih ip ↔
      (ih = 1 ∧ ip = max 0 (min 1
        ((P.I0 + (P.drp - T) / (2 * P.wb)) / (1 - P.psi)))) := by sorry

end BundledPay.Base
