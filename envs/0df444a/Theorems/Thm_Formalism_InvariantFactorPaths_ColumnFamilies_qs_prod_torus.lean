-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_prod_torus
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_prod_torus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:32.784717+00:00
-- url     : https://prove2.me/theorems/fb904495-fb1e-4421-bfed-b8a92fbd318a
-- title:
--   Column Families: qs prod torus
-- statement:
--   The Column Families construction uses the qs prod torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L161-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymStrip.lean#L161-L168

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
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
variable {n : ℕ} [NeZero n]
omit [NeZero n]

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_prod_torus (ε : ℤ) (f : Fin n → ℕ) :
    ∏ x, (AddMonoidAlgebra.single (Pi.single x ε : Fin n → ℤ) (1 : ℤ)) ^ (f x) =
      AddMonoidAlgebra.single (fun x => ε * (f x : ℤ)) 1 := by sorry
