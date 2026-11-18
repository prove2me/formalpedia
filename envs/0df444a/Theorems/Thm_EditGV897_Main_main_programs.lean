-- Prove2me | Theorems.Thm_EditGV897_Main_main_programs
-- name    : EditGV897.Main.main_programs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:57:28.167205+00:00
-- url     : https://prove2.me/theorems/0a9cf3a3-8529-4dd6-9056-38a9a6b70456
-- title:
--   Fixed tape realizations of the main setup, encoder, and decoder
-- statement:
--   For every fixed $t\ge1$, there are fixed finite binary tape programs for the prescribed setup, encoder, and decoder, together with natural constants $A>0,d$, such that for every $n\ge1$ their actual halting executions take at most
--
--   $$A(n+1)^d$$
--
--   transitions. Setup computes the shared parameters from the unary block length and its output has at most this many bits. Encoding computes the specified signed-bound codeword from the parameters and any message in its declared message domain. For every received word of length at most $n+t$, decoding computes the specified candidate-search and image-inversion function, using the empty list when that function returns no candidate.
--
--   This is an operational realization of the algorithms used in the proof of Theorem 1. The transition count includes parsing, legal-script generation, Gaussian elimination, integer arithmetic, and output writing. The empty-list convention on unsuccessful search specifies the program output without imposing a rejection claim on the code.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.1, §4.1–4.2, equations (11)–(12), and proof of Theorem 1, printed pp.7–13 / PDF pp.8–14

import Definitions.Def_EditGV897_Main_Codec
open EditGV897.Main

theorem EditGV897.Main.main_programs (t : ℕ) (ht : 1 ≤ t) :
    ∃ (constructor encoder decoder : Program) (A d : ℕ), 0 < A ∧
      ∀ n : ℕ, 1 ≤ n →
        let F := canonicalFamily t n
        let P := setup t n
        (parametersCode P).length ≤ polyBudget A d n ∧
        Runs constructor (unary n) (parametersCode P) (polyBudget A d n) ∧
        (∀ u : Word (messageLength P),
          Runs encoder (editEncoderInput P u) (wordCode (encodeWord F P u)) (polyBudget A d n)) ∧
        (∀ y : List Bit, y.length ≤ n + t →
          Runs decoder (editDecoderInput P y) (bitCode ((decodeList t P y).getD []))
            (polyBudget A d n)) := by sorry
