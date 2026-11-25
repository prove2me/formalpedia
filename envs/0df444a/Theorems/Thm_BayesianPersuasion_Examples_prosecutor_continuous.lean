-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_prosecutor_continuous
-- name    : BayesianPersuasion.Examples.prosecutor_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:06:39.607499+00:00
-- url     : https://prove2.me/theorems/61fa8b5c-11a3-57fd-bd00-b1374ea77a77
-- title:
--   Examples: prosecutor continuous
-- statement:
--   The Examples construction uses the prosecutor continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L27-L28
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L27-L28

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.prosecutor_continuous (ω : Fin 2) : Continuous (fun a => prosecutor a ω) := by sorry
