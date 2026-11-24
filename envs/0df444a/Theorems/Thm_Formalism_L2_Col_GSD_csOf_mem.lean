-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_csOf_mem
-- name    : Formalism.L2.Col.GSD.csOf_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:44.79075+00:00
-- url     : https://prove2.me/theorems/7bdb954a-49bc-4b77-a1a7-b106b8179a44
-- title:
--   GSD: cs Of mem
-- statement:
--   The GSD construction uses the cs Of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1043-L1054
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1043-L1054

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

theorem Formalism.L2.Col.GSD.csOf_mem (h : S.Ok) (s : S.Sec) {M : Type} [AddCommGroup M] [Module K M] [Module (𝓞 K) M]
    [IsScalarTower (𝓞 K) K M] (N : Submodule (𝓞 K) M) (F : S.D → M) (hF : ∀ d, F d ∈ N) (n : ℕ)
    (hn : ∀ c, (S.toCSDOf h s).wt c ∣ n) : (n : 𝓞 K) • S.csOf h s F ∈ N := by sorry
