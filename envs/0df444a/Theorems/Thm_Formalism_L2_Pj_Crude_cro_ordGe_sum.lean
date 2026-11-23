-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_sum
-- name    : Formalism.L2.Pj.Crude.cro_ordGe_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:43.137805+00:00
-- url     : https://prove2.me/theorems/ddd8f20e-c00d-4419-aa17-f3e9a61beaf3
-- title:
--   Crude: cro ord Ge sum
-- statement:
--   The Crude construction uses the cro ord Ge sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L65-L69

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeOrd
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.cro_ordGe_sum {t : ℕ} {ι : Type} (s : Finset ι) (f : ι → PS k n d) (hf : ∀ i ∈ s, OrdGe t (f i)) :
    OrdGe t (∑ i ∈ s, f i) := by sorry
