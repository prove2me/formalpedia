-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_mem_cond_of_euler_eigen
-- name    : Formalism.InvariantFactorPaths.L4.mem_cond_of_euler_eigen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:11.406467+00:00
-- url     : https://prove2.me/theorems/ed12ce83-5b11-424b-ab50-9c4644da4cbe
-- title:
--   L4: mem cond of euler eigen
-- statement:
--   The L4 construction uses the mem cond of euler eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L393-L422
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/ResInto.lean#L393-L422

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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}

theorem Formalism.InvariantFactorPaths.L4.mem_cond_of_euler_eigen [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ) :
    ∀ (o : ℕ) (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), F ∈ YCond p LL (K + 1) Mt →
      ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F = ((o : ℕ) : ℚ_[p]) • F → F ∈ YCond p LL K Mt := by sorry
