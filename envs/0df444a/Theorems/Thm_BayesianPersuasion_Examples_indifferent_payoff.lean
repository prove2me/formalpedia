-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_indifferent_payoff
-- name    : BayesianPersuasion.Examples.indifferent_payoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:16.82085+00:00
-- url     : https://prove2.me/theorems/7420b59b-6728-5447-93cd-83a10a5b9560
-- title:
--   Examples: indifferent payoff
-- statement:
--   The Examples construction uses the indifferent payoff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L71-L73
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L71-L73

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.indifferent_payoff : senderPayoff judge prosecutor indifferent = 1 := by sorry
