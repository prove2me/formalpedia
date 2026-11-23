-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_SM_map
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:51:38.392672+00:00
-- url     : https://prove2.me/theorems/18ad0a13-09d3-46a2-8373-c1bcec64f853
-- title:
--   Column Families: qs SM map
-- statement:
--   The Column Families construction uses the qs SM map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L123-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QsSymDMatEq.lean#L123-L126

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_BCoreT
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
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
variable {n : ℕ}

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_SM_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (G : Matrix (Fin n) (Fin n) A) (b : ℕ)
    (α β : SymIdx n b) : f (qs_SM G b α β) = qs_SM (G.map f) b α β := by sorry
