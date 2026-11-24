-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_nval_factProd_le
-- name    : Formalism.L2.Pj.Crude.nval_factProd_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:22.506126+00:00
-- url     : https://prove2.me/theorems/c6fe7f51-3973-4d0e-84ae-e6b5c9d39b03
-- title:
--   Crude: nval fact Prod le
-- statement:
--   The Crude construction uses the nval fact Prod le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L146-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L146-L166

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

theorem Formalism.L2.Pj.Crude.nval_factProd_le (ho : OverLa la V ι e) {σ : Type} (α : σ →₀ ℕ) :
    nval V e (((α.prod fun _ t => t.factorial : ℕ) : K')) ≤
      (((ramOverZ la : ℝ) * (α.degree : ℝ) / ((resCharOf la : ℝ) - 1) : ℝ) : EReal) := by sorry
