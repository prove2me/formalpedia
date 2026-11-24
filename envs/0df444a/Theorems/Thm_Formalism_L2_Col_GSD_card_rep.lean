-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_card_rep
-- name    : Formalism.L2.Col.GSD.card_rep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:49.846916+00:00
-- url     : https://prove2.me/theorems/092cdce2-a24f-4dfd-a74d-976d70961790
-- title:
--   GSD: card rep
-- statement:
--   The GSD construction uses the card rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1366-L1370
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1366-L1370

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K)

theorem Formalism.L2.Col.GSD.card_rep (s : (tv K).Sec) (d : Option ℤˣ) :
    Nat.card (MulAction.stabilizer ℤˣ (s.rep ((tv K).cls d))) = Nat.card (MulAction.stabilizer ℤˣ d) := by sorry
