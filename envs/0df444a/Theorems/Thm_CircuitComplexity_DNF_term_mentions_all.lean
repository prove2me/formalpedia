-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_term_mentions_all
-- name    : CircuitComplexity.DNF.term_mentions_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:22.445596+00:00
-- url     : https://prove2.me/theorems/b192a90c-289a-425c-a640-e2f12ea8be4b
-- title:
--   DNF: term mentions all
-- statement:
--   If `φ : DNF N` computes a flip-sensitive function, every satisfiable term
--   mentions all N variables.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L250-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L250-L272

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity

theorem CircuitComplexity.DNF.term_mentions_all (φ : DNF N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x)
    (term : List (Literal N)) (hterm : term ∈ φ.terms)
    (x : BitString N) (hsat : term.all (fun l => l.eval x) = true) :
    ∀ i : Fin N, ∃ l ∈ term, l.var = i := by sorry
