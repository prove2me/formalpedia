-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_phi_mono
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_phi_mono
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:03.980157+00:00
-- url     : https://prove2.me/theorems/98c82bb4-eccb-4ed7-b528-a6b8f94928b5
-- title:
--   Column Families: qh phi mono
-- statement:
--   The Column Families construction uses the qh phi mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhMemDualWeyl.lean#L69-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhMemDualWeyl.lean#L69-L72

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_phi_mono (d : Fin n × Fin n →₀ ℕ) (r : R) :
    qhPhi R n (monomial d r) = monomial (Finsupp.mapDomain Prod.snd d) (monomial d r) := by sorry
