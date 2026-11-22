-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_prefixOverlap_le
-- name    : DeciSigma1.Holes.Tail.card_prefixOverlap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:01.905306+00:00
-- url     : https://prove2.me/theorems/0ea35119-575e-4454-b23b-80ad60e6cf99
-- title:
--   Tail: card prefix Overlap le
-- statement:
--   Among candidate rays of the word `v` with distinct onsets, at most `N - 1` have a
--   `PrefixOverlap` with the ray `u`: the corresponding cuts of `W u`, at or before its first
--   rejected cut, carry distinct live states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L338-L368
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L338-L368

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_TerminalRays
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Tactic.Linarith
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_RayCompatibility
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Arithmetic DeciSigma1.Readers DeciSigma1.Words
open DeciSigma1.Automata DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable [DecidableEq α] [Fintype S]
    [DecidableEq S] {M : StructuralReader α S k} {W : Fin k → List α}
  {u v : Fin k} {Ωu : Ray α} {κ : Type} (R : Finset κ) (Ωc : κ → Ray α) (Ec : κ → ℕ)
omit [DecidableEq S]

theorem DeciSigma1.Holes.Tail.card_prefixOverlap_le (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hAu : Ωu.onset ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hAc : ∀ r ∈ R, (Ωc r).onset ≤ Ec r) (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PrefixOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by sorry
