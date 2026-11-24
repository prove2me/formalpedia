-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qd_minor_unitri
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qd_minor_unitri
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:16:17.178954+00:00
-- url     : https://prove2.me/theorems/746ddff7-d104-4790-9e3d-706ab28c782f
-- title:
--   Column Families: qd minor unitri
-- statement:
--   The Column Families construction uses the qd minor unitri property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L38-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/HighestVectorsEqLattice.lean#L38-L65

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsEqLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qd_minor_unitri {R : Type} [CommRing R] (u : GL (Fin n) R) (h1 : ∀ a, u.val a a = 1)
    (h2 : ∀ a b, b < a → u.val a b = 0) (mu : Fin n → ℤ) (c : ↥(TCols mu))
    (J : {J : Finset (Fin n) // J.card = colH mu c}) :
    evGL u (minorC J.1 (canT mu c).1 J.2 (canT mu c).2) = if J = canT mu c then 1 else 0 := by sorry
