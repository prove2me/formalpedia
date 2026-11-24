-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_evGLR_N
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_N
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:55.223712+00:00
-- url     : https://prove2.me/theorems/59a2d9c3-6633-4122-b26c-431c290c2c59
-- title:
--   Column Families: qh ev GLR N
-- statement:
--   The Column Families construction uses the qh ev GLR N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L154-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L154-L160

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_evGLR_N {R' : Type} [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') (s : ℕ) (hs : s ≤ n)
    (J : Fin s → Fin n) :
    evGLR g (qhN R s hs J) = Matrix.det (Matrix.of fun p q : Fin s => g.val (Fin.castLE hs p) (J q)) := by sorry
