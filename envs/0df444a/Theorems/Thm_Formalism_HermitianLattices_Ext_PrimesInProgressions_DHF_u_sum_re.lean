-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_DHF_u_sum_re
-- name    : Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:19:32.643792+00:00
-- url     : https://prove2.me/theorems/47b759c2-406d-4efc-abd0-9a12b85e6f92
-- title:
--   DHF: u sum re
-- statement:
--   The DHF construction uses the u sum re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishB.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/JacobiCharacterSums/PNTDHFinishB.lean#L22-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHFinishB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF

theorem Formalism.HermitianLattices.Ext.PrimesInProgressions.DHF.u_sum_re (η : ℝ) {N : ℕ} (w : Fin N → ℂ) (j : ℕ) :
    (∑ i, ((η : ℂ) / w i) ^ j).re = η ^ j * (∑ i, 1 / (w i) ^ j).re := by sorry
