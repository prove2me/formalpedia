-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DepPage_le_eLam
-- name    : Formalism.L2.Pj.DepPage.le_eLam
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:46:45.320193+00:00
-- url     : https://prove2.me/theorems/3b778cc1-1eb7-5ec3-8301-0a7249ca5609
-- title:
--   Dep Page: le e Lam
-- statement:
--   The Dep Page construction uses the le e Lam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PlaceBelow.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/PlaceBelow.lean#L160-L164

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_VAtVNeBot
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
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
open Formalism Formalism.L2 Formalism.L2.Pj
open MvPowerSeries NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem Formalism.L2.Pj.DepPage.le_eLam (Q : DepPage) (eL : ℕ) (nu : ℝ) (p : ℕ) :
    (eL : ℝ) * (Q.T : ℝ) * nu ≤ (Q.eLam eL nu p : ℝ) := by sorry
