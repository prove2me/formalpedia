-- Prove2me | Theorems.Thm_DeciSigma1_Words_chain_stop_from
-- name    : DeciSigma1.Words.chain_stop_from
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:28.24719+00:00
-- url     : https://prove2.me/theorems/cb38dc7f-8108-4762-8719-ee8691fecb2e
-- title:
--   Words: chain stop from
-- statement:
--   If every chain of `t` that starts at a length at least `b₀` has at most `S` steps, the chain
--   from `bs ≥ b₀` that continues while `suffixReturnGap t b ≤ g b` stops at some `b ≥ bs` where
--   `suffixReturnGap t b` is undefined or exceeds `g b`, and `b` is at most the `S`-fold iterate of
--   `b ↦ b + g b` at `bs`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L341-L383
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L341-L383

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α : Type}
variable [DecidableEq α]

theorem DeciSigma1.Words.chain_stop_from {t : List α} {b₀ S : ℕ} (hS : ChainBoundFrom t b₀ S) (g : ℕ → ℕ)
    (hg : Monotone g) {bs : ℕ} (hbs : b₀ ≤ bs) :
    ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h := by sorry
