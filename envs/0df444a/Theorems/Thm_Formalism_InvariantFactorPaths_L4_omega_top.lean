-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_omega_top
-- name    : Formalism.InvariantFactorPaths.L4.omega_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:28.24238+00:00
-- url     : https://prove2.me/theorems/4137f200-49b7-4aac-b419-5711cde65ea1
-- title:
--   L4: omega top
-- statement:
--   The L4 construction uses the omega top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L498-L537
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/OmegaInjectiveHolds.lean#L498-L537

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_Sl2RaisePowSuccLowerApplyEq
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_EArith
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_OmegaInjectiveHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.omega_top (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (c : ℤ) (o : ℕ)
    (th : Fin r → ℤ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hP : x ∈ Pol p r (setLast LL (o + 1)))
    (hF : x ∈ FreeOf p (Fin.last K, ρ)) (hx : x ∈ HWC p LL (K + 1) (univ.erase ρ) th) (β : Fin r → ℤ)
    (htop : ∀ γ, phiW β < phiW γ → cw p K γ x = 0) :
    cw p K β (Omega p LL c ρ x) = ((Enum ρ c o th β : ℤ) : ℚ_[p]) • cw p K β x := by sorry
