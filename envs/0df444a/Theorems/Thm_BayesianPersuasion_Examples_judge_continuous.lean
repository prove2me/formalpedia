-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_judge_continuous
-- name    : BayesianPersuasion.Examples.judge_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:44.696403+00:00
-- url     : https://prove2.me/theorems/e4b68247-552b-434c-add1-963319ff7f5d
-- title:
--   Examples: judge continuous
-- statement:
--   The Examples construction uses the judge continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L24-L25
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L24-L25

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.judge_continuous (ω : Fin 2) : Continuous (fun a => judge a ω) := by sorry
