-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_card_stab_smul
-- name    : Formalism.L2.Col.GSD.card_stab_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:03.425082+00:00
-- url     : https://prove2.me/theorems/43f64d45-cc86-4e84-9f52-0db92b79fd82
-- title:
--   GSD: card stab smul
-- statement:
--   The GSD construction uses the card stab smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L25-L35

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

theorem Formalism.L2.Col.GSD.card_stab_smul (g : S.G) (d : S.D) :
    Nat.card (MulAction.stabilizer S.G (g • d)) = Nat.card (MulAction.stabilizer S.G d) := by sorry
