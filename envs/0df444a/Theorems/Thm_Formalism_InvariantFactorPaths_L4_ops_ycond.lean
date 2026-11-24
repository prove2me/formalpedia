-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_ops_ycond
-- name    : Formalism.InvariantFactorPaths.L4.ops_ycond
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:36:42.45641+00:00
-- url     : https://prove2.me/theorems/cb02a75f-8ff9-48b7-a8cd-6412f0dc2822
-- title:
--   L4: ops ycond
-- statement:
--   The L4 construction uses the ops ycond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/RaisingKeepsEarlyLetters.lean#L53-L67

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
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

theorem Formalism.InvariantFactorPaths.L4.ops_ycond {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (T : Module.End ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hT : T ∈ FockB.Ops {v : Fin N × Fin r | j ≤ (v.1 : ℕ)}) :
    ∀ x ∈ YCond p LL j Mt, T x ∈ YCond p LL j Mt := by sorry
