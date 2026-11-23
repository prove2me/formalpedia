-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_resL_glAct
-- name    : Formalism.InvariantFactorPaths.L4.resL_glAct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:33:09.388049+00:00
-- url     : https://prove2.me/theorems/cbf64d0d-a9af-4573-ba35-76e4f807fb03
-- title:
--   L4: res L gl Act
-- statement:
--   The L4 construction uses the res L gl Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L69-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L69-L85

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
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
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.L4.resL_glAct {N r : ℕ} (LL : Letters N) (j : ℕ) (c d : Fin r) (v : Fin N × Fin r) (e : ℕ)
    (h : ∀ i : Fin N, (i : ℕ) < j → (i, c) ≠ v ∧ (i, d) ≠ v) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    resL p v e (glAct p LL j c d x) = glAct p LL j c d (resL p v e x) := by sorry
