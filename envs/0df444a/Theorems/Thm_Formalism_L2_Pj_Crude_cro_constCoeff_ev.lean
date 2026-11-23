-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_cro_constCoeff_ev
-- name    : Formalism.L2.Pj.Crude.cro_constCoeff_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:40:54.038609+00:00
-- url     : https://prove2.me/theorems/e943d4a5-493f-4fc3-8b30-8f818e2d6128
-- title:
--   Crude: cro const Coeff ev
-- statement:
--   The Crude construction uses the cro const Coeff ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L97-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeOrd.lean#L97-L116

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

theorem Formalism.L2.Pj.Crude.cro_constCoeff_ev {m : ℕ} (a : Fin m → Pt k n d) (ha : ∀ p i, constantCoeff (a p i) = 0)
    (f : PS k m d) : constantCoeff (ev a f) = constantCoeff f := by sorry
