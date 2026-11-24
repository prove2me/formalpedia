-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_lin
-- name    : Formalism.L2.Pj.Crude.cro_ordGe_lin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:08.995812+00:00
-- url     : https://prove2.me/theorems/011a2dbb-d68d-4b1c-bc2a-65096c6f1194
-- title:
--   Crude: cro ord Ge lin
-- statement:
--   The Crude construction uses the cro ord Ge lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L92-L95

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

theorem Formalism.L2.Pj.Crude.cro_ordGe_lin {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (b : Fin n) (v : Fin d → k) :
    OrdGe t (Lin b v f) := by sorry
