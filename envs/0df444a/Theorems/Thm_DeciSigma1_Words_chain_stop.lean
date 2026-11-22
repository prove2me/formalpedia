-- Prove2me | Theorems.Thm_DeciSigma1_Words_chain_stop
-- name    : DeciSigma1.Words.chain_stop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:07:58.493142+00:00
-- url     : https://prove2.me/theorems/5eeca3de-3bcc-4301-a6fc-7a75ca250845
-- title:
--   Words: chain stop
-- statement:
--   If every chain of `t` has at most `S` steps, the chain from `bs` that continues while
--   `suffixReturnGap t b ≤ g b` stops at some `b ≥ bs` where `suffixReturnGap t b` is undefined or
--   exceeds `g b`, and `b` is at most the `S`-fold iterate of `b ↦ b + g b` at `bs`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L388-L391
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/SuffixChains.lean#L388-L391

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

theorem DeciSigma1.Words.chain_stop {t : List α} {S : ℕ} (hS : ChainBound t S) (g : ℕ → ℕ) (hg : Monotone g)
    (bs : ℕ) : ∃ b, bs ≤ b ∧ b ≤ (fun b => b + g b)^[S] bs ∧
      ∀ h, suffixReturnGap t b = some h → g b < h := by sorry
