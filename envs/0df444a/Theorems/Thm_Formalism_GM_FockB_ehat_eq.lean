-- Prove2me | Theorems.Thm_Formalism_GM_FockB_ehat_eq
-- name    : Formalism.GM.FockB.ehat_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:45.82062+00:00
-- url     : https://prove2.me/theorems/b7ce3723-d388-48d1-96e0-949600cfafec
-- title:
--   Fock B: ehat eq
-- statement:
--   The Fock B construction uses the ehat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L430-L435
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L430-L435

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} (D : BlockData N)
variable (p : ℕ) [Fact p.Prime]

theorem Formalism.GM.FockB.ehat_eq (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp =
      chainE (wA D) (eA D) (zA D) (sA D) (jA D j jp) (LA D) := by sorry
