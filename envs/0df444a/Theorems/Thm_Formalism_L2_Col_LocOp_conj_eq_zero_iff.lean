-- Prove2me | Theorems.Thm_Formalism_L2_Col_LocOp_conj_eq_zero_iff
-- name    : Formalism.L2.Col.LocOp.conj_eq_zero_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:53.946727+00:00
-- url     : https://prove2.me/theorems/64513253-6cc0-4ea9-989e-411deb35e481
-- title:
--   Loc Op: conj eq zero iff
-- statement:
--   The Loc Op construction uses the conj eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L493-L508
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L493-L508

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
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}

theorem Formalism.L2.Col.LocOp.conj_eq_zero_iff (g : S.G) (g' : S'.G) (k : S.V →ₗ[K] S'.V) :
    (S'.ρ g') ∘ₗ k ∘ₗ (S.ρ g) = 0 ↔ k = 0 := by sorry
