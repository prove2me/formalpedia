-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_restr_card_stab
-- name    : Formalism.L2.Col.GSD.restr_card_stab
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:26.947133+00:00
-- url     : https://prove2.me/theorems/eb6c83b2-b649-41c1-9c6b-88e26c3eef39
-- title:
--   GSD: restr card stab
-- statement:
--   The GSD construction uses the restr card stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L668-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L668-L673

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
variable (S : GSD K)

theorem Formalism.L2.Col.GSD.restr_card_stab (T : SubMulAction S.G S.D) (t : T) :
    Nat.card (MulAction.stabilizer (S.restr T).G (show (S.restr T).D from t)) =
      Nat.card (MulAction.stabilizer S.G (t : S.D)) := by sorry
