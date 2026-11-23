-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_OrdGe_mul
-- name    : Formalism.L2.Pj.Crude.OrdGe.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:21.287837+00:00
-- url     : https://prove2.me/theorems/8a344117-72ec-49da-a9e5-4c68d038c0c8
-- title:
--   Ord Ge: mul
-- statement:
--   The Ord Ge construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L31-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L31-L51

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

theorem Formalism.L2.Pj.Crude.OrdGe.mul {a b : ℕ} {f g : PS k n d} (hf : OrdGe a f) (hg : OrdGe b g) : OrdGe (a + b) (f * g) := by sorry
