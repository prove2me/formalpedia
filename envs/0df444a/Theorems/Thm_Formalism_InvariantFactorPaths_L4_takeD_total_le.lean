-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_takeD_total_le
-- name    : Formalism.InvariantFactorPaths.L4.takeD_total_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:06:20.376063+00:00
-- url     : https://prove2.me/theorems/79bff855-1103-5dc5-94ff-3bdf1250cdb9
-- title:
--   L4: take D total le
-- statement:
--   The L4 construction uses the take D total le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L263-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/GramBoundUnconditionalOfSat.lean#L263-L295

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {N : ℕ}

theorem Formalism.InvariantFactorPaths.L4.takeD_total_le (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (a : ℕ) (Yl n₀ dd : Fin T.t → ℕ)
    (hS : ∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i)
    (hdeg : ∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a)
    (n : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n₀ i + dd i * (Yl i - 1)) (i : Fin T.t) :
    ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ 2 * a := by sorry
