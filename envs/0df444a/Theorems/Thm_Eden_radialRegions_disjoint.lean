-- Prove2me | Theorems.Thm_Eden_radialRegions_disjoint
-- name    : Eden.radialRegions_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:32.267892+00:00
-- url     : https://prove2.me/theorems/e724ef87-589f-5970-ac9c-99cbad279af0
-- title:
--   Eden: radial Regions disjoint
-- statement:
--   The Eden construction uses the radial Regions disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L51-L54
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L51-L54

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.radialRegions_disjoint : Disjoint innerRadialRegion outerRadialRegion := by sorry
