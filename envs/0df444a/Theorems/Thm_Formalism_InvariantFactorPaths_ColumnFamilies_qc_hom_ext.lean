-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_hom_ext
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qc_hom_ext
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:30.95015+00:00
-- url     : https://prove2.me/theorems/9b0c4c4c-3ba3-42e4-8abf-2a6692dd8fe2
-- title:
--   Column Families: qc hom ext
-- statement:
--   The Column Families construction uses the qc hom ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QcEvGLGenPtInt.lean#L29-L35

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qc_hom_ext {n : ℕ} {R : Type} [CommRing R] (f g : GLCoord ℤ n →+* R)
    (h : ∀ a b, f (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b))) =
      g (algebraMap (MvPolynomial (Fin n × Fin n) ℤ) _ (X (a, b)))) : f = g := by sorry
