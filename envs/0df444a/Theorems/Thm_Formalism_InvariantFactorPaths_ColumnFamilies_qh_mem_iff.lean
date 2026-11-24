-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_mem_iff
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qh_mem_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:37:55.762576+00:00
-- url     : https://prove2.me/theorems/69a5e69d-6ca8-4efe-bcd0-3fecb996f45c
-- title:
--   Column Families: qh mem iff
-- statement:
--   The Column Families construction uses the qh mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L48-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QhDetZpowMem.lean#L48-L80

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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qh_mem_iff (mu : Fin n → ℤ) (f : GLCoord R n) :
    f ∈ inducedSections R mu ↔ ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R') (u : Fin n → R'ˣ),
      (∀ a c : Fin n, a < c → b.val a c = 0) → (∀ a, (u a : R') = b.val a a) →
      evGLR (b * g) f = ((∏ a, u a ^ mu a : R'ˣ) : R') * evGLR g f := by sorry
