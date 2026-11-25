-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_chgSec_nab
-- name    : Formalism.L2.Col.GSD.chgSec_nab
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:43:59.433845+00:00
-- url     : https://prove2.me/theorems/ec27ac2d-ac55-4761-a32a-40b6dbcf0501
-- title:
--   GSD: chg Sec nab
-- statement:
--   The GSD construction uses the chg Sec nab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L164-L169

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

theorem Formalism.L2.Col.GSD.chgSec_nab (h : S.Ok) (s s' : S.Sec) (f : (S.toCSDOf h s).Forms) :
    (∀ c, (S.chgSec h s s' f).1 c ∈ S.Nab (s'.rep c)) ↔ ∀ c, f.1 c ∈ S.Nab (s.rep c) := by sorry
