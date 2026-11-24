-- Prove2me | Theorems.Thm_Formalism_GM_M_Q_sat
-- name    : Formalism.GM.M.Q_sat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:12.027678+00:00
-- url     : https://prove2.me/theorems/d1b9499e-2355-4f53-ba31-98fd9d916a8b
-- title:
--   M: Q sat
-- statement:
--   The M construction uses the Q sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L708-L746
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L708-L746

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

theorem Formalism.GM.M.Q_sat (j : Fin D.T.t → ℕ) (jp : ℕ) (Q : MvPolynomial (BVar N r D.T.t) ℚ_[p])
    (hQ : Q ∈ Submodule.span ℚ_[p] (Bset (p := p) D j jp)) (hint : IsInt Q) :
    Q ∈ Submodule.span ℤ_[p] (Bset (p := p) D j jp) := by sorry
