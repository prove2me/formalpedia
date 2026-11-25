-- Prove2me | Theorems.Thm_BayesianPersuasion_Examples_interval_action_optimum
-- name    : BayesianPersuasion.Examples.interval_action_optimum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T09:09:07.271768+00:00
-- url     : https://prove2.me/theorems/288dfd92-9648-45d0-b37c-11acfdf8f2fd
-- title:
--   Examples: interval action optimum
-- statement:
--   The theorem applies also to a continuum of actions, not only finite games.
--
--   Source: https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L98-L109
-- source:
--   https://github.com/Arthur742Ramos/bayesian-persuasion-lean/blob/6bb350283717128bcd625daf93da18fe199e13d9/BayesianPersuasion/Examples.lean#L98-L109

module
public import Definitions.Def_BayesianPersuasion_Theorems
public import Definitions.Def_BayesianPersuasion_Examples
set_option autoImplicit true
@[expose] public section
public section
open BayesianPersuasion BayesianPersuasion.Examples
open Set Finset
attribute [local instance] BayesianPersuasion.Examples._p2m_local_instance_545c504162_17

theorem BayesianPersuasion.Examples.interval_action_optimum :
    ∃ (n : ℕ) (_ : n ≤ 4) (π : Signal (Fin 2) n),
      signalValue quadraticReceiver linearSender prior π =
        concavification quadraticReceiver linearSender prior.val ∧
      ∀ (m : ℕ) (σ : Signal (Fin 2) m),
        signalValue quadraticReceiver linearSender prior σ ≤
          signalValue quadraticReceiver linearSender prior π := by sorry
