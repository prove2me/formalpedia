-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefColsR_RR_spec
-- name    : Formalism.L2.Indef.IndefColsR.RR_spec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:17.756426+00:00
-- url     : https://prove2.me/theorems/e889e4e9-b582-48d7-8ff9-7275034d429f
-- title:
--   Indef Cols R: RR spec
-- statement:
--   The Indef Cols R construction uses the RR spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L332-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L332-L342

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
import Theorems.Thm_Formalism_L2_Indef_IndefRows_RR_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Indef.IndefColsR
variable {Bs : DefBase K} {Df : DefSide Bs} {Dc : DefCols Df} {Sp : SPer Dc} {N : IndefNum Bs}
  (S : IndefColsR Df Dc Sp N)

theorem Formalism.L2.Indef.IndefColsR.RR_spec (hG : LatticeGlue) (wf : Df.WF) :
    Submodule.IsLattice K S.RR ∧ ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal S.RR =
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (S.ι (S.μ w)) (Df.abelian₂ (S.μ w))) := by sorry
