-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_prosecutor_strict_gain
-- name    : BayesianPersuasion.Examples.prosecutor_strict_gain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:08:34.163698+00:00
-- url     : https://prove2.me/theorems/9fa7381b-384d-5138-84be-cf57a07a66bb
-- title:
--   Examples: prosecutor strict gain
-- statement:
--   The paper's prosecutor gains from 0 to 3/5 at prior guilt probability 3/10.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L83-L91
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L83-L91

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.prosecutor_strict_gain :
    ∃ π : Signal (Fin 2) 2,
      signalValue judge prosecutor prior π = 3 / 5 ∧
      senderPayoff judge prosecutor prior < signalValue judge prosecutor prior π := by sorry
