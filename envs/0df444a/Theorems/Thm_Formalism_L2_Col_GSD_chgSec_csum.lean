-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_chgSec_csum
-- name    : Formalism.L2.Col.GSD.chgSec_csum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:44:01.384944+00:00
-- url     : https://prove2.me/theorems/7def6796-0dc8-4abb-a244-1d1924796973
-- title:
--   GSD: chg Sec csum
-- statement:
--   The GSD construction uses the chg Sec csum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L154-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L154-L162

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

theorem Formalism.L2.Col.GSD.chgSec_csum (h : S.Ok) (s s' : S.Sec) (f f' : (S.toCSDOf h s).Forms) :
    (S.toCSDOf h s').csum (S.chgSec h s s' f).1 (S.chgSec h s s' f').1 = (S.toCSDOf h s).csum f.1 f'.1 := by sorry
