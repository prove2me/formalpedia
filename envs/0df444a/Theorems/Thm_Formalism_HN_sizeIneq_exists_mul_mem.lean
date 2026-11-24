-- Prove2me | Theorems.Thm_Formalism_HN_sizeIneq_exists_mul_mem
-- name    : Formalism.HN.sizeIneq_exists_mul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:42.119201+00:00
-- url     : https://prove2.me/theorems/707c9b8a-6e3b-4c7c-b8ed-08cdbd53eef7
-- title:
--   HN: size Ineq exists mul mem
-- statement:
--   The HN construction uses the size Ineq exists mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L19-L21

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

theorem Formalism.HN.sizeIneq_exists_mul_mem (A : Submodule (𝓞 K) V) (x : V)
    (hx : x ∈ Submodule.span K (A : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by sorry
