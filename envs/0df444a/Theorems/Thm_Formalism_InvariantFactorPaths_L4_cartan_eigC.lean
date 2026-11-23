-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_cartan_eigC
-- name    : Formalism.InvariantFactorPaths.L4.cartan_eigC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:59:04.991967+00:00
-- url     : https://prove2.me/theorems/384c07f9-5979-41cf-afb5-177b124799e2
-- title:
--   L4: cartan eig C
-- statement:
--   The L4 construction uses the cartan eig C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L10-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FirstWeightLeOfSupport.lean#L10-L20

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.cartan_eigC (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) (μ : Fin r → ℤ)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ WtSpC p LL j Cs μ) (c : Fin r) (hc : c ∈ Cs) :
    glAct p LL j c c x = ((μ c : ℤ) : ℚ_[p]) • x := by sorry
