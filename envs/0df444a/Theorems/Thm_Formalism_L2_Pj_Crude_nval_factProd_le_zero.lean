-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_nval_factProd_le_zero
-- name    : Formalism.L2.Pj.Crude.nval_factProd_le_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:22.09473+00:00
-- url     : https://prove2.me/theorems/84da19d5-7765-436f-ae9a-986063a26aad
-- title:
--   Crude: nval fact Prod le zero
-- statement:
--   The Crude construction uses the nval fact Prod le zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L168-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L168-L181

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open NumberField IsDedekindDomain Formalism.L2.Pj
open scoped WithZero
variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))
  {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K'] {ι : K →+* K'} {e : ℕ}

theorem Formalism.L2.Pj.Crude.nval_factProd_le_zero (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) (hα : ∀ s, α s < resCharOf la) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤ 0 := by sorry
