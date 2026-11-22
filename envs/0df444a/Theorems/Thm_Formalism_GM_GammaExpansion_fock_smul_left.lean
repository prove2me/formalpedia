-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_smul_left
-- name    : Formalism.GM.GammaExpansion.fock_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:56.993809+00:00
-- url     : https://prove2.me/theorems/2fe67adf-147e-4c45-84ae-c5f3088d86b2
-- title:
--   Gamma Expansion: fock smul left
-- statement:
--   The Gamma Expansion construction uses the fock smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L136-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L136-L140

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.GammaExpansion
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]

theorem Formalism.GM.GammaExpansion.fock_smul_left (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p (c • F) G = c * M.fock p F G := by sorry
