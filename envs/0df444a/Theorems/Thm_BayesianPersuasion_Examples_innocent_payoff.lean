-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_innocent_payoff
-- name    : BayesianPersuasion.Examples.innocent_payoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:03.077225+00:00
-- url     : https://prove2.me/theorems/be467a6c-da62-5b72-bcd9-a60357ea4da4
-- title:
--   Examples: innocent payoff
-- statement:
--   The Examples construction uses the innocent payoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L67-L69
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L67-L69

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.innocent_payoff : senderPayoff judge prosecutor innocent = 0 := by sorry
