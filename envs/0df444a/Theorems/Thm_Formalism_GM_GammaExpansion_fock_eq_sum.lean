-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_eq_sum
-- name    : Formalism.GM.GammaExpansion.fock_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:49.61565+00:00
-- url     : https://prove2.me/theorems/ae2d3e34-857f-46c1-9f31-d7a9601da20a
-- title:
--   Gamma Expansion: fock eq sum
-- statement:
--   The Gamma Expansion construction uses the fock eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L113-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L113-L118

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

theorem Formalism.GM.GammaExpansion.fock_eq_sum (F G : MvPolynomial σ ℚ_[p]) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    M.fock p F G = ∑ m ∈ s, F.coeff m * G.coeff m * fw p m := by sorry
