-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_rays_no_positiveCycle
-- name    : DeciSigma1.Holes.Tail.rays_no_positiveCycle
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:38.30319+00:00
-- url     : https://prove2.me/theorems/90ad2981-37a1-430b-9191-93a9d040ed56
-- title:
--   Tail: rays no positive Cycle
-- statement:
--   If every ray that is not periodic at its first rejected cut has no forbidden overlap with
--   any other ray, closed walks of the ray system avoid these rays; if moreover a potential `L`
--   satisfies every constraint between two of the other rays, the ray system has no positive
--   cycle.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L442-L490
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L442-L490

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
public import Mathlib.Order.Nat
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Candidates
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Holes.Tail.rays_no_positiveCycle [DecidableEq α] [Fintype S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : StructuralReader α S k) (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) (L : ι → ℤ)
        (isM : ι → Prop)
    (hM : ∀ v, isM v → J v < (Ω v).onset ∧ ∀ u,
        u ≠ v → NoForbiddenRayOverlap (Ω v) (Ω u) (J v) (J u))
    (hT : ∀ i j, ¬ isM i → ¬ isM j → i ≠ j → ∀ a b, b ≤ J j →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → L i + ((b : ℤ) - a + 1) ≤ L j) :
    ¬ (raySystem M st Ω J).HasPositiveCycle := by sorry
