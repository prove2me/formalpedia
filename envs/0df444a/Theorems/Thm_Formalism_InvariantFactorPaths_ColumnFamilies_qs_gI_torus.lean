-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_gI_torus
-- name    : Formalism.InvariantFactorPaths.ColumnFamilies.qs_gI_torus
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:22:07.340798+00:00
-- url     : https://prove2.me/theorems/a8838c9f-3182-48f6-ba17-f18d3cf54be0
-- title:
--   Column Families: qs g I torus
-- statement:
--   The Column Families construction uses the qs g I torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L160-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/SymDStrip.lean#L160-L170

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymStrip
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SymDStrip
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

theorem Formalism.InvariantFactorPaths.ColumnFamilies.qs_gI_torus : (qs_gI n).transpose.map (evGL (torusPt n)) =
    Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1 : ℤ)) (1 : ℤ) := by sorry
