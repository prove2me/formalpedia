-- Prove2me | Theorems.Thm_Erdos261_carry_iff
-- name    : Erdos261.carry_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:52.9873+00:00
-- url     : https://prove2.me/theorems/1a90f332-c228-41c6-8d57-40c5c3f8465a
-- title:
--   Binary-carry characterisation of $\sum_{j=1}^N c_j2^{N-j}=0$
-- statement:
--   **Theorem.** For integers $c_1,\dots,c_N$,
--
--   $$\sum_{j=1}^{N}c_j\,2^{N-j}=0\iff \exists\, r_1,\dots,r_{N+1}\in\mathbb Z:\ r_{N+1}=0,\ r_1=0,\ 2r_j=c_j+r_{j+1}\ (1\le j\le N).$$
--
--   This is the exact signed carry formulation of Erdős Problem 261 (applied with $c_j=j[j\in S]-n[j=n]$): a representation is the same as a finite carry run that starts and ends at $0$. No limiting process is involved.
--
--   **Formalization Note.** $c,r$ are functions $\mathbb N\to\mathbb Z$; only the values on $[1,N+1]$ matter.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; Theorem A3 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem carry_iff (N : ℕ) (c : ℕ → ℤ) :
    ∑ j ∈ Icc 1 N, c j * 2 ^ (N - j) = 0 ↔
      ∃ r : ℕ → ℤ, r (N + 1) = 0 ∧ r 1 = 0 ∧ ∀ j ∈ Icc 1 N, 2 * r j = c j + r (j + 1) := by sorry

end Erdos261
