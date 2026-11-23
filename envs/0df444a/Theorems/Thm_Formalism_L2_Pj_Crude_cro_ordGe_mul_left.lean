-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_mul_left
-- name    : Formalism.L2.Pj.Crude.cro_ordGe_mul_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:41:13.254936+00:00
-- url     : https://prove2.me/theorems/d201cb26-8fd2-4e73-adf3-9df014ce45aa
-- title:
--   Crude: cro ord Ge mul left
-- statement:
--   The Crude construction uses the cro ord Ge mul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L71-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L71-L73

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

theorem Formalism.L2.Pj.Crude.cro_ordGe_mul_left {t : ℕ} (g : PS k n d) {f : PS k n d} (hf : OrdGe t f) : OrdGe t (g * f) := by sorry
