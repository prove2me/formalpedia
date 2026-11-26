-- Prove2me | Theorems.Thm_Eden_mapLyapunovDimension_isGreatest
-- name    : Eden.mapLyapunovDimension_isGreatest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:25:27.324669+00:00
-- url     : https://prove2.me/theorems/885aad4b-ff68-4b89-aec4-ba6606d738b3
-- title:
--   Eden: map Lyapunov Dimension is Greatest
-- statement:
--   The Eden construction uses the map Lyapunov Dimension is Greatest property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L137-L139
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/SingularValueFunction.lean#L137-L139

import Definitions.Def_Eden_SingularValues
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Definitions.Def_Eden_SingularValueFunction
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.mapLyapunovDimension_isGreatest {A : PhaseSpace →ₗ[ℝ] PhaseSpace}
    (hA : Function.Injective A) : IsGreatest (admissibleDimensions A) (mapLyapunovDimension A) := by sorry
