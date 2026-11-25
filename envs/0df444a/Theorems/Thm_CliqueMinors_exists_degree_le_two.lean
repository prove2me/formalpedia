-- Prove2me | Theorems.Thm_CliqueMinors_exists_degree_le_two
-- name    : CliqueMinors.exists_degree_le_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:46.042141+00:00
-- url     : https://prove2.me/theorems/31b25aa2-9472-4c0a-819c-6ebf4cd5c09e
-- title:
--   Clique Minors: exists degree le two
-- statement:
--   **Dirac (1952).** A nonempty finite graph without a `K₄` minor has a vertex of degree at most
--   two.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L742-L750
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L742-L750

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}

theorem CliqueMinors.exists_degree_le_two [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : ∃ v, G.degree v ≤ 2 := by sorry
