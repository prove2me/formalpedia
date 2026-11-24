-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_DDop_apply
-- name    : Formalism.InvariantFactorPaths.L4.DDop_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:21:24.533227+00:00
-- url     : https://prove2.me/theorems/45221d34-ef7b-419b-b35b-65f34cf80840
-- title:
--   L4: DDop apply
-- statement:
--   The L4 construction uses the DDop apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L62-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/DerivativeDividedIntegral.lean#L62-L66

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeDividedIntegral
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
variable (LL : Letters (K + 1)) (Cs : Finset (Fin r)) (a : Fin r)

theorem Formalism.InvariantFactorPaths.L4.DDop_apply (F : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    DDop p LL Cs a F = X (Fin.last K, a) * ProjS.eulL (fun c : Fin r => (Fin.last K, c)) F +
        ∑ b ∈ Cs, X (Fin.last K, b) * glAct p LL K a b F := by sorry
