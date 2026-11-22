-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_mkRay_eq
-- name    : DeciSigma1.Holes.Tail.mkRay_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:58.8005+00:00
-- url     : https://prove2.me/theorems/f65703f3-9e29-48fd-bb11-c1512ecd25a6
-- title:
--   Tail: mk Ray eq
-- statement:
--   The Tail construction uses the mk Ray eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L156-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L156-L157

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_WindowChains
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayFamilies
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.mkRay_eq {dflt : Ray α} {x : List α} {c c' : ℕ} (h : c < c' ∧ c' ≤ x.length) :
    mkRay dflt x c c' = repeatFactorRay x c c' h.1 h.2 := by sorry
