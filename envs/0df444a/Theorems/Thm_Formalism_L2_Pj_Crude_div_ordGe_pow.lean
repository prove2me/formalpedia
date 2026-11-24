-- Prove2me | Theorems.Thm_Formalism_L2_Pj_Crude_div_ordGe_pow
-- name    : Formalism.L2.Pj.Crude.div_ordGe_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:58:28.274904+00:00
-- url     : https://prove2.me/theorems/5b3c6567-e740-4297-89f3-cc83a8d513c5
-- title:
--   Crude: div ord Ge pow
-- statement:
--   The Crude construction uses the div ord Ge pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L54-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/CrudeDiv.lean#L54-L59

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeBase
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeDiv
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
variable {k : Type} [CommRing k] {d n : ℕ}

theorem Formalism.L2.Pj.Crude.div_ordGe_pow {a : ℕ} {f : PS k n d} (hf : OrdGe a f) (e : ℕ) : OrdGe (a * e) (f ^ e) := by sorry
