-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Tail_pumpFactor_period_of_snoc
-- name    : DeciSigma1.Holes.Tail.pumpFactor_period_of_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:09:40.241331+00:00
-- url     : https://prove2.me/theorems/b4b552df-d783-4ae1-9456-16ff34eff2d4
-- title:
--   Tail: pump Factor period of snoc
-- statement:
--   A function `F` of words that is updated letter by letter, `F (w ++ [a]) = G (F w) a`, and
--   takes the same value on the prefixes of length `c < c'` repeats with period `c' - c` from `c` on
--   along the pumped factor.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L609-L625
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Tail/Rays.lean#L609-L625

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
variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}

theorem DeciSigma1.Holes.Tail.pumpFactor_period_of_snoc {β : Type*} (F : List α → β) (G : β → α → β)
    (hF : ∀ w a, F (w ++ [a]) = G (F w) a) (hcc : c < c') (hc' : c' ≤ x.length)
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) {p : ℕ} (hp : c ≤ p)
    (hpL : p + (c' - c) ≤ c + L) :
    F ((pumpFactor x c c' L).take (p + (c' - c))) = F ((pumpFactor x c c' L).take p) := by sorry
