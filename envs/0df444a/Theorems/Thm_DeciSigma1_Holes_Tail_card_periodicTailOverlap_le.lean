-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_card_periodicTailOverlap_le
-- name    : DeciSigma1.Holes.Tail.card_periodicTailOverlap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T14:58:07.786934+00:00
-- url     : https://prove2.me/theorems/7b7e6839-92fd-49a5-ad45-b84b114273cf
-- title:
--   Tail: card periodic Tail Overlap le
-- statement:
--   If every candidate of `v` agrees with `W v` on at least `(N + 1) ν` letters from its onset,
--   where `ν` is the period of `u`, at most `N - 1` candidates have a `PeriodicTailOverlap` with
--   `u`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L413-L501
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/RayCompatibility.lean#L413-L501

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

theorem DeciSigma1.Holes.Tail.card_periodicTailOverlap_le (hu : M.Eligible W u) {Eu : ℕ} (hΩu : RayAgrees Ωu (W u) Eu)
    (hJu : M.firstRejection W u ≤ Eu) (hc : ∀ r ∈ R, RayAgrees (Ωc r) (W v) (Ec r))
    (hrun : ∀ r ∈ R, (Ωc r).onset + (Fintype.card S + 1) * Ωu.period ≤ Ec r)
    (hJc : ∀ r ∈ R, M.firstRejection W v < (Ωc r).onset)
    (hinj : Set.InjOn (fun r => (Ωc r).onset) R) :
    (R.filter (fun r => PeriodicTailOverlap (Ωc r) Ωu (M.firstRejection W v)
        (M.firstRejection W u))).card ≤
      Fintype.card S - 1 := by sorry
