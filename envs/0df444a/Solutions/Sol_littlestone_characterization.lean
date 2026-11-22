-- Prove2me | solution 1 for littlestone_characterization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:45:22.186131+00:00
-- url     : https://prove2.me/submissions/9235e15e-c827-4d96-ac5a-ca7b699ee65a

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Theorem_Online
public import Theorems.Thm_forward_direction
public import Theorems.Thm_backward_direction

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution (X : Type)
    (C : ConceptClass X Bool) :
    OnlineLearnable X Bool C ↔ LittlestoneDim X C < ⊤ :=
  ⟨forward_direction X C, backward_direction X C⟩
