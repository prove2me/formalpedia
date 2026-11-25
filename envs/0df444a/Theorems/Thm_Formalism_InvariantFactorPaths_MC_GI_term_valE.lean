-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_MC_GI_term_valE
-- name    : Formalism.InvariantFactorPaths.MC.GI.term_valE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:58:55.664241+00:00
-- url     : https://prove2.me/theorems/54e1e1a1-ca10-5f81-820c-324ca94d965a
-- title:
--   GI: term val E
-- statement:
--   The GI construction uses the term val E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L18-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/PartnerMeanProofs/GamIntC.lean#L18-L141

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

theorem Formalism.InvariantFactorPaths.MC.GI.term_valE (LL : Letters (N + 1)) (hr : 1 ≤ r) (B : ℕ)
    (hB : Nat.log p (LL.total + LL.deg (Fin.last N) + r) ≤ B) (j a a' : ℕ)
    (hj : j ≤ LL.deg (Fin.last N)) (ha : a ≤ j) (ha' : a' ≤ j)
    (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ)
    (hk : ∀ k : Fin N, δv δ (Fin.castSucc (Fin.castSucc k)) = LL.deg (Fin.castSucc k))
    (hW : δv δ (Fin.castSucc (Fin.last N)) = LL.deg (Fin.last N) - j)
    (hY : δv δ (Fin.last (N + 1)) = LL.total - (j - a))
    (d1 d2 : ℕ) (hd1 : padicValNat p a.factorial ≤ padicValNat p d1) (hd1' : d1 ≠ 0)
    (hd2 : padicValNat p a'.factorial ≤ padicValNat p d2) (hd2' : d2 ≠ 0) :
    -(kapE N r B : ℤ) + ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a).factorial : ℤ))) +
      ((((r * B : ℕ) : ℤ) - 2 * (padicValNat p (j - a').factorial : ℤ))) -
      (padicValNat p (j.choose a * j.choose a' * d1 * d2 * a'.factorial *
        ∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) : ℤ) +
      (padicValNat p ((LL.deg (Fin.last N)).choose j * j.factorial ^ 2 * LL.total.factorial *
        ∏ i, (LL.deg i).factorial) : ℤ) ≤ 0 := by sorry
