-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TA2_isPt_ext
-- name    : Formalism.FourierDecayAlt.P.TA2.isPt_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:28.847805+00:00
-- url     : https://prove2.me/theorems/64927433-6c6d-4128-b69e-a2fae8107df8
-- title:
--   TA2: is Pt ext
-- statement:
--   The TA2 construction uses the is Pt ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OffDiagonalSchurComplement.lean#L32-L42

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2

theorem Formalism.FourierDecayAlt.P.TA2.isPt_ext {E : Type} [Zero E] {i s : ℕ} (hs : 1 ≤ s) (hsi : s ≤ i) {h : Pt E} {t : E}
    (hh : IsPt (i - s) h) (ht : t ≠ 0) : IsPt i (ext h s t) := by sorry
