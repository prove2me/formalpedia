-- Prove2me | Theorems.Thm_DeciSigma1_Arithmetic_periodic_run_stable
-- name    : DeciSigma1.Arithmetic.periodic_run_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:29.811959+00:00
-- url     : https://prove2.me/theorems/b86a532d-4a51-4634-8637-56b76e29a74d
-- title:
--   Arithmetic: periodic run stable
-- statement:
--   Along an infinite word of period `d`, the states of a run at cuts of at least `|S| · d`
--   repeat with period `d · |S|!`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L302-L323
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Arithmetic/FinitePaths.lean#L302-L323

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_FinitePaths
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Arithmetic
variable {β : Type*}
open DeciSigma1.Readers DeciSigma1.Words
variable {α S : Type} {k : ℕ}

theorem DeciSigma1.Arithmetic.periodic_run_stable [Fintype S] (T : Table α S k) (q : S) (ξ : ℕ → α) {d p : ℕ}
    (hξ : StreamPeriod ξ d) (hp : Fintype.card S * d ≤ p) (m : ℕ) :
    runFrom T.step q (streamPrefix ξ (p + m * (d * (Fintype.card S).factorial))) =
      runFrom T.step q (streamPrefix ξ p) := by sorry
