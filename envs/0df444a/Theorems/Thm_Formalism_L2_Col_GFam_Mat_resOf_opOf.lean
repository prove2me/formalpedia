-- Prove2me | Theorems.Thm_Formalism_L2_Col_GFam_Mat_resOf_opOf
-- name    : Formalism.L2.Col.GFam.Mat.resOf_opOf
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:45:54.022364+00:00
-- url     : https://prove2.me/theorems/80e56b07-2bff-5de4-b8e1-d0c93e6730d9
-- title:
--   Mat: res Of op Of
-- statement:
--   The Mat construction uses the res Of op Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1183-L1193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/GSetLemmas.lean#L1183-L1193

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
open Formalism.L2.Col.GFam
variable (F : GFam K)

theorem Formalism.L2.Col.GFam.Mat.resOf_opOf {F F' : GFam K} (M : Mat F F') (h : F.Ok) (h' : F'.Ok) (s : ∀ b, (F.mem b).Sec)
    (s' : ∀ b', (F'.mem b').Sec) (φ : F.Forms) :
    (F'.resOf h' s' (M.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((F.toCSDOf h s).wt c : K))⁻¹) (M.atReps s s') (F.resOf h s φ).1 := by sorry
