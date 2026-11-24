-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_map_span_mem
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_map_span_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:21:08.901692+00:00
-- url     : https://prove2.me/theorems/1fef0cd4-ffd0-40e1-a473-e6c180bd942d
-- title:
--   Column Families: qc map span mem
-- statement:
--   The Column Families construction uses the qc map span mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L57-L63

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_map_span_mem {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S : Set A)
    (y : A) (hy : y ∈ Submodule.span ℤ S) : φ y ∈ Submodule.span F (φ '' S) := by sorry
