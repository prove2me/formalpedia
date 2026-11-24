-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_compP_mem_intPol
-- name    : Formalism.InvariantFactorPaths.L4.compP_mem_intPol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:21.708063+00:00
-- url     : https://prove2.me/theorems/44c5b681-a7aa-48fa-af8b-4e9526f865a6
-- title:
--   L4: comp P mem int Pol
-- statement:
--   The L4 construction uses the comp P mem int Pol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L340-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L340-L348

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersModP
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem Formalism.InvariantFactorPaths.L4.compP_mem_intPol {p : ℕ} [Fact p.Prime] {σ : Type} (Pr : (σ →₀ ℕ) → Prop) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ IntPol p σ) : compP Pr x ∈ IntPol p σ := by sorry
