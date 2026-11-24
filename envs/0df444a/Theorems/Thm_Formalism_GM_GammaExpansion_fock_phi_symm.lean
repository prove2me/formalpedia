-- Prove2me | Theorems.Thm_Formalism_GM_GammaExpansion_fock_phi_symm
-- name    : Formalism.GM.GammaExpansion.fock_phi_symm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:22.29338+00:00
-- url     : https://prove2.me/theorems/5c17b60b-fc87-49b4-9aaa-60d5ff9e8eac
-- title:
--   Gamma Expansion: fock phi symm
-- statement:
--   The Gamma Expansion construction uses the fock phi symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L223-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean#L223-L228

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

theorem Formalism.GM.GammaExpansion.fock_phi_symm (o n z : ℕ) (u v : MvPolynomial σ ℚ_[p]) :
    M.fock p (tiePhi w e o n z u) v = M.fock p (tiePhi w e o n z v) u := by sorry
