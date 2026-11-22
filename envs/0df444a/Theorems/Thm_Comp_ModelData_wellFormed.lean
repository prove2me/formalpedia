-- Prove2me | Theorems.Thm_Comp_ModelData_wellFormed
-- name    : Comp.ModelData.wellFormed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T23:37:22.970804+00:00
-- url     : https://prove2.me/theorems/ef43e392-2498-4e64-ac0e-4710fd48f66e
-- title:
--   Model Data: well Formed
-- statement:
--   **The payoff.** The structural conditions and the stochastic one give a well-formed game. Split
--       deliberately: `Shape` is pure `ℕ` and goes by `decide`, and only `Stochastic` costs rational
--       arithmetic.
--
--       Note how little the totality of the kernel costs here. `Stochastic` is a property of the
--       transitions a model declares -- checkable one at a time as it is built -- and the pairs the
--       model does *not* declare inherit it, because padding sends each of them to a declared
--       transition (`transAt_mem`) and a terminal state's self-loop carries weight `1`.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L784-L790
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/ModelData.lean#L784-L790

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
set_option autoImplicit true
open Comp

theorem Comp.ModelData.wellFormed (d : ModelData) [NeZero d.nAct1] [NeZero d.nAct2]
    (hs : d.Shape) (h2 : d.Stochastic) : d.toCsgQ.WellFormed := by sorry
