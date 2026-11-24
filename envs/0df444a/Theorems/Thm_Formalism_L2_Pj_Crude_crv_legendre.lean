-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_crv_legendre
-- name    : Formalism.L2.Pj.Crude.crv_legendre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:45.246257+00:00
-- url     : https://prove2.me/theorems/e5b24017-1e0b-41aa-a3b1-2000c83f866f
-- title:
--   Crude: crv legendre
-- statement:
--   The Crude construction uses the crv legendre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L138-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeVal.lean#L138-L144

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

theorem Formalism.L2.Pj.Crude.crv_legendre {σ : Type} (p : ℕ) [Fact p.Prime] (α : σ →₀ ℕ) :
    (p - 1) * padicValNat p (α.prod fun _ t => t.factorial) ≤ α.degree := by sorry
