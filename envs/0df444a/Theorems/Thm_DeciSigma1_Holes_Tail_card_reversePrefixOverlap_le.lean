-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_reversePrefixOverlap_le
-- name    : DeciSigma1.Holes.Tail.card_reversePrefixOverlap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:57:58.5314+00:00
-- url     : https://prove2.me/theorems/aff06539-9dbc-4754-ae28-ea71cd7a9f08
-- title:
--   Tail: card reverse Prefix Overlap le
-- statement:
--   Among candidate rays of the word `v` with distinct onsets, at most `N - 1` have a
--   `ReversePrefixOverlap` with the ray `u`: the stretch of `u` occurs in `W v` ending at the onset
--   of the candidate, and the starts of these occurrences carry distinct live states.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L374-L407
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L374-L407

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

theorem DeciSigma1.Holes.Tail.card_reversePrefixOverlap_le (hv : M.Eligible W v)
    (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hAc : ∀ r ∈ R, (Ωc r).onset ≤ Ec r) (hJc : ∀ r ∈ R, M.firstRejection W v < (Ωc r).onset)
    (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => ReversePrefixOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by sorry
