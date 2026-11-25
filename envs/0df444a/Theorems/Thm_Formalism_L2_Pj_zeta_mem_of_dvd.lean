-- Prove2me | Theorems.Thm_Formalism_L2_Pj_zeta_mem_of_dvd
-- name    : Formalism.L2.Pj.zeta_mem_of_dvd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:37:35.333232+00:00
-- url     : https://prove2.me/theorems/3073131a-d7b5-485b-b073-bf0f1bbca6e8
-- title:
--   Pj: zeta mem of dvd
-- statement:
--   The Pj construction uses the zeta mem of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DepthPins.lean#L28-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DepthPins.lean#L28-L41

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DepthPins
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem Formalism.L2.Pj.zeta_mem_of_dvd {l : Level H} (c : Coeff l) {g : ℕ} (hg : g ∣ l.M') (h0 : l.M' ≠ 0) : zeta g ∈ c.F := by sorry
