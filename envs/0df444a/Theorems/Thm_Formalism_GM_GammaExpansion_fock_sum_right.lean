-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_sum_right
-- name    : Formalism.GM.GammaExpansion.fock_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:18.262125+00:00
-- url     : https://prove2.me/theorems/68e2e3a4-1f45-423e-ba40-4355cfffe8c6
-- title:
--   Gamma Expansion: fock sum right
-- statement:
--   The Gamma Expansion construction uses the fock sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L161-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L161-L164

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

theorem Formalism.GM.GammaExpansion.fock_sum_right {ι : Type} (t : Finset ι) (F : MvPolynomial σ ℚ_[p]) (G : ι → MvPolynomial σ ℚ_[p]) :
    M.fock p F (∑ i ∈ t, G i) = ∑ i ∈ t, M.fock p F (G i) := by sorry
