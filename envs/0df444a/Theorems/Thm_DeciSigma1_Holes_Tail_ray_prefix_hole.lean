-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_ray_prefix_hole
-- name    : DeciSigma1.Holes.Tail.ray_prefix_hole
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:10:19.877027+00:00
-- url     : https://prove2.me/theorems/240b7a04-a179-4d6c-9ee0-9efe8cffe4d9
-- title:
--   Tail: ray prefix hole
-- statement:
--   Suppose every target cut of an admitted pair is at most `J`,
--   `L j > J j + maxOnset + 2 · maxPeriod`, no admitted comparison of a ray with itself with `a ≤ b`
--   has equal infinite suffixes, and `L` solves the ray system. Then the prefixes of length `L` carry
--   no admitted comparison, between any two rays or a ray and itself.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L1021-L1053
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L1021-L1053

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata
variable {ι : Type}
variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]
variable {M}

theorem DeciSigma1.Holes.Tail.ray_prefix_hole [DecidableEq S] (st : ι → S) (Ω : ι → Ray α) (J L : ι → ℕ)
    (hK : ∀ j b p, b ≤ L j → M.admitted p (rayState M (st j) (Ω j) b) = true → b ≤ J j)
    (hlong : ∀ j, J j + maxOnset Ω + 2 * maxPeriod Ω < L j)
    (hself : ∀ i a b, b ≤ J i → a ≤ b →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st i) (Ω i) b) = true →
      ¬ ∀ t, (Ω i).stream (a + t) = (Ω i).stream (b + t))
    (hsat : (raySystem M st Ω J).Sat (fun i => (L i : ℤ))) :
    ∀ i j, ∀ pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
      (streamPrefix (Ω j).stream (L j)), M.admitted pq.1 pq.2 = false := by sorry
