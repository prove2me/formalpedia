-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_ordGe_pderiv
-- name    : Formalism.L2.Pj.Crude.cro_ordGe_pderiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:11.096708+00:00
-- url     : https://prove2.me/theorems/cf7cbaa4-0fc1-455b-8e74-d714dfdd77bc
-- title:
--   Crude: cro ord Ge pderiv
-- statement:
--   The Crude construction uses the cro ord Ge pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L75-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L75-L90

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

theorem Formalism.L2.Pj.Crude.cro_ordGe_pderiv {t : ℕ} {f : PS k n d} (hf : OrdGe (t + 1) f) (i : Fin n × Fin d) :
    OrdGe t (pderiv k i f) := by sorry
