-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_MC_GI_termF_IVPE
-- name    : Formalism.InvariantFactorPaths.MC.GI.termF_IVPE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:47:14.272217+00:00
-- url     : https://prove2.me/theorems/98750c43-0abf-49a6-a9f5-be96426dbc9a
-- title:
--   GI: term F IVPE
-- statement:
--   The GI construction uses the term F IVPE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L148-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L148-L292

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_TheoremMCB
import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_PartnerMeanProofs_GamIntC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.MC Formalism.InvariantFactorPaths.MC.GI
open MvPolynomial Finset Formalism.GM Formalism.GM.M Formalism.GM.gammaIntegralityLemmas
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}

theorem Formalism.InvariantFactorPaths.MC.GI.termF_IVPE (LL : Letters (N + 1)) (ρ : Fin r) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (z j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (β γ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hβd : δv β + (j - a) • eWY = (LL.snoc LL.total).deg) (hβp : β (xW ρ) ≤ β (yE ρ))
    (hγd : δv γ + (j - a') • eWY = (LL.snoc LL.total).deg) (hγp : γ (xW ρ) ≤ γ (yE ρ))
    (h h' : ℚ_[p])
    (hh : ‖h‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))))
    (hh' : ‖h'‖ ≤ (p : ℝ) ^ ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ)))) :
    IVP p (LL.total + LL.deg (Fin.last N))
      (fun m => (p : ℚ_[p]) ^ (kapE N r B) * termF LL ρ z j a a' β γ h h' m) := by sorry
