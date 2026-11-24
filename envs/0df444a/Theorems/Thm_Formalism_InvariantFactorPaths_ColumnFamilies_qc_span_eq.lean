-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_span_eq
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_span_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:07.458692+00:00
-- url     : https://prove2.me/theorems/c69705a7-5c0b-4643-bd2e-eebc715584d1
-- title:
--   Column Families: qc span eq
-- statement:
--   The Column Families construction uses the qc span eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L65-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L65-L73

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_span_eq {A B F : Type} [CommRing A] [CommRing B] [Field F] [Module F B] (φ : A →+* B) (S T : Set A)
    (h : Submodule.span ℤ S = Submodule.span ℤ T) : Submodule.span F (φ '' S) = Submodule.span F (φ '' T) := by sorry
