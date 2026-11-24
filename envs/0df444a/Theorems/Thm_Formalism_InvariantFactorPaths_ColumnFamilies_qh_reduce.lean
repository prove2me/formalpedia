-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_reduce
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_reduce
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:20:20.589062+00:00
-- url     : https://prove2.me/theorems/f529bc85-53d3-4068-8324-898f7fe05064
-- title:
--   Column Families: qh reduce
-- statement:
--   The Column Families construction uses the qh reduce property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/InducedSectionsSpanStatement.lean#L11-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/InducedSectionsSpanStatement.lean#L11-L45

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhCountAll
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_InducedSectionsSpanStatement
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_reduce [IsDomain R] (mu : Fin n → ℤ) (f : GLCoord R n) (hf : f ∈ inducedSections R mu) :
    ∃ (k : ℕ) (Q : MvPolynomial (Fin n × Fin n) R), (∀ a, 0 ≤ mu a + k) ∧
      f = ((qhDet R n ^ (-(k : ℤ)) : (GLCoord R n)ˣ) : GLCoord R n) *
        algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∧
      Q ∈ Formalism.GradedWeylDivisibility.dualWeyl R n n (fun a => (mu a + k).toNat) := by sorry
