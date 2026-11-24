-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_det
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_det
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.356599+00:00
-- url     : https://prove2.me/theorems/ccaaea8c-0e5c-4bca-97d2-eac3a8c57fb3
-- title:
--   Column Families: qh ev GLR det
-- statement:
--   The Column Families construction uses the qh ev GLR det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L130-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L130-L132

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_det {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') :
    evGLR g ((qhDet R n : (GLCoord R n)ˣ) : GLCoord R n) = g.val.det := by sorry
