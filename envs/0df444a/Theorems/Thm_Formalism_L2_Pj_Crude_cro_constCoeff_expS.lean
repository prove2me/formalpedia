-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_constCoeff_expS
-- name    : Formalism.L2.Pj.Crude.cro_constCoeff_expS
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:31.238518+00:00
-- url     : https://prove2.me/theorems/913b5ab5-d55a-4520-8adb-a28f773398f8
-- title:
--   Crude: cro const Coeff exp S
-- statement:
--   The Crude construction uses the cro const Coeff exp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L118-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L118-L125

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

theorem Formalism.L2.Pj.Crude.cro_constCoeff_expS [Algebra ℚ k] (s : PS k n d) (hs : constantCoeff s = 0) :
    constantCoeff (FB.expS k s) = 1 := by sorry
