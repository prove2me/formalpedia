-- Prove2me | Theorems.Thm_Formalism_GM_FockB_letterAt_val
-- name    : Formalism.GM.FockB.letterAt_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:02.524605+00:00
-- url     : https://prove2.me/theorems/b1c9f93e-663a-4f64-a42d-bc4b08594f8b
-- title:
--   Fock B: letter At val
-- statement:
--   The Fock B construction uses the letter At val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L451-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L451-L452

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
variable {D}

theorem Formalism.GM.FockB.letterAt_val {k : ℕ} (h : k ≤ N - 1) : (D.letterAt k : ℕ) = k := by sorry
