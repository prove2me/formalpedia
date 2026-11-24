-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_smul_right
-- name    : Formalism.GM.GammaExpansion.fock_smul_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:14.6168+00:00
-- url     : https://prove2.me/theorems/45e74a27-f2a3-4b9a-afe3-563b67b9ad60
-- title:
--   Gamma Expansion: fock smul right
-- statement:
--   The Gamma Expansion construction uses the fock smul right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L157-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L157-L159

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

theorem Formalism.GM.GammaExpansion.fock_smul_right (c : ℚ_[p]) (F G : MvPolynomial σ ℚ_[p]) :
    M.fock p F (c • G) = c * M.fock p F G := by sorry
