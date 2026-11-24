-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_E_pow
-- name    : Formalism.GM.GammaExpansion.fock_E_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:28.294877+00:00
-- url     : https://prove2.me/theorems/c51599e2-e192-43e1-9fe7-73b2098539fd
-- title:
--   Gamma Expansion: fock E pow
-- statement:
--   The Gamma Expansion construction uses the fock E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L214-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L214-L221

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
variable {r : ℕ} (w e : Fin r → σ)

theorem Formalism.GM.GammaExpansion.fock_E_pow (j : ℕ) (a b : MvPolynomial σ ℚ_[p]) :
    M.fock p ((tieE w e ^ j) a) b = M.fock p a ((tieF w e ^ j) b) := by sorry
