-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtSpC_pow
-- name    : Formalism.InvariantFactorPaths.L4.wtSpC_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:04:11.460875+00:00
-- url     : https://prove2.me/theorems/a17504d4-2eec-4036-b64b-ff96ca6a8689
-- title:
--   L4: wt Sp C pow
-- statement:
--   The L4 construction uses the wt Sp C pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L186-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/FiltrationBotHolds.lean#L186-L202

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_MulEarlyLettersHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FiltrationBotHolds
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
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} (LL : Letters (K + 1))

theorem Formalism.InvariantFactorPaths.L4.wtSpC_pow (hv : LL.vec (Fin.last K) = true) (ρ : Fin r) (e o : ℕ) (Cs : Finset (Fin r)) (w : Fin r → ℤ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :
    X (Fin.last K, ρ) ^ e * h ∈ WtSpC p LL (K + 1) Cs w ↔
      h ∈ WtSpC p (setLast LL o) (K + 1) Cs (shiftWt w ρ e) := by sorry
