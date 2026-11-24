-- Prove2me | Theorems.Thm_Formalism_HN_sizeIneq_rk
-- name    : Formalism.HN.sizeIneq_rk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:56.23595+00:00
-- url     : https://prove2.me/theorems/a4863013-56d6-457e-8b63-33de03f86666
-- title:
--   HN: size Ineq rk
-- statement:
--   The HN construction uses the size Ineq rk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L44-L58

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Lemmata_GeneralBFactSecondTail_Imports
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeIneq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN
variable {K : Type*} [Field K] [NumberField K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {W : Type*} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

theorem Formalism.HN.sizeIneq_rk [FiniteDimensional K V] (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) + rkK (A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)) =
      rkK A := by sorry
