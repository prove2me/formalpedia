-- Prove2me | Theorems.Thm_Eden_globalLyapunovDimension_attractor_eight
-- name    : Eden.globalLyapunovDimension_attractor_eight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:58:32.249482+00:00
-- url     : https://prove2.me/theorems/374c2951-5d48-5b54-9403-d48a4e06e807
-- title:
--   Eden: global Lyapunov Dimension attractor eight
-- statement:
--   The Eden construction uses the global Lyapunov Dimension attractor eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L133-L136
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeDimension.lean#L133-L136

import Definitions.Def_Eden_SingularValueFunction
import Definitions.Def_Eden_VolumeGrowth
import Definitions.Def_Eden_FiniteTimeDimension
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.globalLyapunovDimension_attractor_eight :
    globalLyapunovDimension 8 attractor = 9 / 2 := by sorry
