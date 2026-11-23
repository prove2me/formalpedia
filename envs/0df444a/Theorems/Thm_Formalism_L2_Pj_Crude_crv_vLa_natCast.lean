-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crv_vLa_natCast
-- name    : Formalism.L2.Pj.Crude.crv_vLa_natCast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:45:01.311776+00:00
-- url     : https://prove2.me/theorems/f21a326e-4a6f-4da3-a64f-a3cb546b2ad9
-- title:
--   Crude: crv v La nat Cast
-- statement:
--   The Crude construction uses the crv v La nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L88-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L88-L111

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

theorem Formalism.L2.Pj.Crude.crv_vLa_natCast {N : ℕ} (hN : N ≠ 0) :
    vLa la ((N : ℕ) : K) = (padicValNat (resCharOf la) N * ramOverZ la : ℕ) := by sorry
