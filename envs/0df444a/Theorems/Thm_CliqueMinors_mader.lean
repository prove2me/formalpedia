-- Prove2me | Theorems.Thm_CliqueMinors_mader
-- name    : CliqueMinors.mader
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:40:38.797674+00:00
-- url     : https://prove2.me/theorems/62701c89-1bf1-4203-ac9b-f1496ea13af3
-- title:
--   Clique Minors: mader
-- statement:
--   **Mader's theorem (1967).** A nonempty finite graph whose average degree is at least
--   `2 ^ (r - 2)`, i.e. `2 ^ r · |V| ≤ 8 · |E|`, has the complete graph `K_r` as a minor.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L731-L738
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L731-L738

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

theorem CliqueMinors.mader [Fintype V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ)
    (h : 2 ^ r * Fintype.card V ≤ 8 * G.edgeFinset.card) :
    IsMinor (⊤ : SimpleGraph (Fin r)) G := by sorry
