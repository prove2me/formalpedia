-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_X_mul_int
-- name    : Formalism.InvariantFactorPaths.L4.glAct_X_mul_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:40:24.908798+00:00
-- url     : https://prove2.me/theorems/04a9f3dc-eaf2-4178-88e5-ed6a40c163ee
-- title:
--   L4: gl Act X mul int
-- statement:
--   The L4 construction uses the gl Act X mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/MulEarlyLettersModP.lean#L63-L72

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
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ)

theorem Formalism.InvariantFactorPaths.L4.glAct_X_mul_int (c : Fin r) (v : Fin N × Fin r) (g : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hg : g ∈ IntPol p (Fin N × Fin r)) : glAct p LL j 0 c (X v) * g ∈ IntPol p (Fin N × Fin r) := by sorry
