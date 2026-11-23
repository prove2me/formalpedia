-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_G_psd
-- name    : Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:36:41.618213+00:00
-- url     : https://prove2.me/theorems/66f4064b-92f0-498b-86b7-2e397f7dd974
-- title:
--   A1: G psd
-- statement:
--   The A1 construction uses the G psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RecursionWithDensities.lean#L302-L309

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {E : Type} [Field E] [DecidableEq E]

theorem Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.G_psd (D : TA.Data E) (Sg : ℕ → ℕ → Finset E) (Th) (hNZ : NZSg Sg) (hK : AxK D)
    (hD : TC.DomMinA D Sg Th) (i s : ℕ) (hs : 1 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1)
    (c : E ⧸ D.La i s) : PSDOn (PT Sg (i - s)) (G (D.La i s) (Sg i s) (Th i s) c) := by sorry
