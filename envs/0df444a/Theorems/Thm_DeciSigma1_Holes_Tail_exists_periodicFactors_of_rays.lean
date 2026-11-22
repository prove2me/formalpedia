-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_exists_periodicFactors_of_rays
-- name    : DeciSigma1.Holes.Tail.exists_periodicFactors_of_rays
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:25.465248+00:00
-- url     : https://prove2.me/theorems/90a79d29-9132-49cf-999d-d1d6b703f83c
-- title:
--   Tail: exists periodic Factors of rays
-- statement:
--   Rays that agree with `x` up to their ends `E i`, with periods at most `P`, give one periodic
--   factor of `x` for each onset: it runs from the onset to the furthest end among the rays with that
--   onset, cut at `cap ≤ |x|`. Every position below `cap` from the onset to the end of one of the
--   rays is covered.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L125-L156
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Candidates.lean#L125-L156

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

theorem DeciSigma1.Holes.Tail.exists_periodicFactors_of_rays [DecidableEq α] {ι : Type*} (s : Finset ι)
    (Ω : ι → Ray α) (E : ι → ℕ) {x : List α} {P cap : ℕ}
    (hag : ∀ i ∈ s, RayAgrees (Ω i) x (E i)) (hP : ∀ i ∈ s, (Ω i).period ≤ P)
    (hcap : cap ≤ x.length) :
    ∃ fs : List PeriodicFactor, fs.length = (s.image fun i => (Ω i).onset).card ∧
      (∀ f ∈ fs, f.Valid x P ∧ f.stop ≤ cap) ∧
      ∀ i ∈ s, ∀ y, (Ω i).onset ≤ y → y < E i → y < cap → Covers fs y := by sorry
