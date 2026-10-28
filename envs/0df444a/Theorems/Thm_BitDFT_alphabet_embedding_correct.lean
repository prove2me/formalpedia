-- Prove2me | Theorems.Thm_BitDFT_alphabet_embedding_correct
-- name    : BitDFT.alphabet_embedding_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T16:47:43.140869+00:00
-- url     : https://prove2.me/theorems/30ec269f-0190-49a6-bf44-be31d2e52f59
-- title:
--   Alphabet embedding preserves exact runs and native binary I/O
-- statement:
--   For any machines M,N and injective symbol map preserving the five distinguished symbols, the lifted machine’s t-step run from any encoded configuration equals the encoding of M’s t-step run. Moreover, every native binary-input halting computation of M with output w is reproduced by the lifted machine at exactly the same t. The finite state set and tape count do not change. No runtime overhead or regularity condition is introduced.
-- source:
--   Actual machine adapter, with a constructed transition table and full-configuration simulation. It resolves alphabet compatibility for later composition; it does not provide buffer placement or a child-machine call on its own.

import Definitions.Def_BitDFT_AlphabetEmbedding
open BitDFT.AlphabetEmbedding IntMul

theorem BitDFT.alphabet_embedding_correct (M N : MultitapeTM) (e : Map M N) :
    (∀ (c : M.Cfg) (t : ℕ), (machine e).step^[t] (embed e c) = embed e (M.step^[t] c)) ∧
    (∀ (x y : List Bool) (t : ℕ) (w : List Bool), M.HaltsWithOutput x y t w →
      (machine e).HaltsWithOutput x y t w) := by sorry
