-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_rayFamily
-- name    : DeciSigma1.Holes.Tail.exists_rayFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:59:01.470411+00:00
-- url     : https://prove2.me/theorems/0a324950-3e0f-4a26-a34a-c7fe0b3f691a
-- title:
--   Tail: exists ray Family
-- statement:
--   Every hole has a ray family at a stable level. Terminal rays come from
--   `exists_terminal_ray` at level `l - 1`; the other rays are chosen in turn
--   (`exists_greedy_choice`), each a candidate without forbidden overlaps with the rays chosen
--   before (`exists_compatible_rayCandidate`). Compatibility is symmetric (`compatible_symm`), so
--   `rays_no_positiveCycle` applies.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L168-L339
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayFamilies.lean#L168-L339

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
variable [Fintype α] [DecidableEq α] [Fintype S] [DecidableEq S]

theorem DeciSigma1.Holes.Tail.exists_rayFamily (C : LevelBounds (Fintype.card α) k (Fintype.card S))
    {M : StructuralReader α S k} {W : Fin k → List α} (hW : M.IsHole W) : Nonempty
        (RayFamily C M W) := by sorry
