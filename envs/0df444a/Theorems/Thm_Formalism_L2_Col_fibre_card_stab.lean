-- Prove2me | Theorems.Thm_Formalism_L2_Col_fibre_card_stab
-- name    : Formalism.L2.Col.fibre_card_stab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:16.231798+00:00
-- url     : https://prove2.me/theorems/8a5e93c5-2872-4090-990f-0785d61adf71
-- title:
--   Col: fibre card stab
-- statement:
--   The Col construction uses the fibre card stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L952-L969
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L952-L969

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
variable {G D D₀ : Type} [Group G] [MulAction G D] [MulAction G D₀] (pr : D → D₀)
  (hpr : ∀ (g : G) (d : D), pr (g • d) = g • pr d)

theorem Formalism.L2.Col.fibre_card_stab (x : D₀) (y : fibre pr hpr x) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G x) y) = Nat.card (MulAction.stabilizer G (y : D)) := by sorry
