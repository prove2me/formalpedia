-- Prove2me | Theorems.Thm_Formalism_GM_M_pre_span_mem
-- name    : Formalism.GM.M.pre_span_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:47.383362+00:00
-- url     : https://prove2.me/theorems/8aeb0e83-b75e-48e9-b68f-ff3d075ab189
-- title:
--   M: pre span mem
-- statement:
--   The M construction uses the pre span mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L662-L671
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L662-L671

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (D : BlockData N)

theorem Formalism.GM.M.pre_span_mem (j : Fin D.T.t → ℕ) (jp : ℕ) (hL : D.LevelOK j jp) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp)) : pre D j jp * Q ∈ D.SSZ p (r := r) := by sorry
