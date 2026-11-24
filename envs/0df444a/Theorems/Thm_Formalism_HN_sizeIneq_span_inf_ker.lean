-- Prove2me | Theorems.Thm_Formalism_HN_sizeIneq_span_inf_ker
-- name    : Formalism.HN.sizeIneq_span_inf_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:29:35.065199+00:00
-- url     : https://prove2.me/theorems/024e94f2-044a-46b5-90bc-2bd313e83e96
-- title:
--   HN: size Ineq span inf ker
-- statement:
--   The HN construction uses the size Ineq span inf ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L23-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/SizeIneq.lean#L23-L42

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

theorem Formalism.HN.sizeIneq_span_inf_ker (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) :
    Submodule.span K ((A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K (A : Set V) ⊓ LinearMap.ker φ := by sorry
