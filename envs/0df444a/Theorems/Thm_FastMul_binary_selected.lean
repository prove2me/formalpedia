-- Prove2me | Theorems.Thm_FastMul_binary_selected
-- name    : FastMul.binary_selected
-- status  : Open
-- author  : @arpcs
-- created : 2026-10-31T03:59:43.099887+00:00
-- url     : https://prove2.me/theorems/47984f6a-1697-46b9-9a4d-3bf72b44efd1
-- title:
--   Theorem 9 — Ordinary binary multiplication with saving $2^{-38}$
-- statement:
--   There exist one deterministic multitape Turing machine $M$, a real constant $C>0$ and an integer threshold $n_0$, all fixed independently of the inputs, such that every two length-$n$ coefficient vectors over $\mathbb F_2$, for every $n\ge1$, have a halted execution producing their complete ordinary polynomial product.
--
--   The literal output contains all $2n-1$ coefficients in ascending degree order, including zeros, and then blanks. Whenever $n\ge n_0$, that execution uses at most
--   $$C n\max\{1,\lceil\log_2 n\rceil\}^{1-2^{-38}}$$
--   transitions. All setup, arithmetic, movement and output steps of the fixed finite program count. Correct termination is required below the threshold too.
--
--   **Formalization Note** The shared platform machine uses one-way tapes, a read-only input and separate output. Conversion from the source/local two-way convention is a proof obligation, not an assumed supplier. This is an open formalization target of an AI-assisted preprint; independent human review and a complete Lean proof remain outstanding.
-- source:
--   Árpád Csizmadia, Ordinary Binary Polynomial Multiplication below n log n: Controlled tensor routing on fixed tapes, version 0.1.0-preprint (2026), Theorem 9 (label thm:main), main.tex lines 1013–1044; https://github.com/arpcs/finite-field-polynomial-multiplication/blob/fb94421e3e6d9f8348a6e5b963b5a62d9c525e95/papers/03-best-binary/main.tex#L1013 .

import Definitions.Def_FastMul_BinaryTask
set_option autoImplicit false

theorem FastMul.binary_selected :
    FastMulPlatform.BinaryTimeBound (1 / 274877906944 : ℚ) := by sorry
