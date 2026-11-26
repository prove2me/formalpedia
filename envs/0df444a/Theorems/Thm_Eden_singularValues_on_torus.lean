-- Prove2me | Theorems.Thm_Eden_singularValues_on_torus
-- name    : Eden.singularValues_on_torus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:01.688384+00:00
-- url     : https://prove2.me/theorems/a2cc01d2-7e0c-457c-a1b8-ba0d6f0ff49c
-- title:
--   Eden: singular Values on torus
-- statement:
--   The Eden construction uses the singular Values on torus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L24-L40
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/OrderedStationarySpectrum.lean#L24-L40

import Definitions.Def_Eden_StationaryFactors
import Definitions.Def_Eden_SingularValues
import Mathlib.Data.List.Sort
import Mathlib.Order.Fin.Basic
import Definitions.Def_Eden_OrderedStationarySpectrum
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.singularValues_on_torus {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t)
    {p : PhaseSpace} (hp : p ∈ torus) :
    (fun i : Fin 5 => (fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) =
      ![Real.exp (2 * t), Real.exp (2 * t), 1, 1, Real.exp (-c * t)] := by sorry
