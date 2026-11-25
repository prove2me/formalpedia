-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_prosecutor_split_value
-- name    : BayesianPersuasion.Examples.prosecutor_split_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:07:38.154266+00:00
-- url     : https://prove2.me/theorems/e6fd72f2-7ee6-4e34-945b-955c70e61cd6
-- title:
--   Examples: prosecutor split value
-- statement:
--   The Examples construction uses the prosecutor split value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L79-L80
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L79-L80

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.prosecutor_split_value : splitValue judge prosecutor weights beliefs = 3 / 5 := by sorry
