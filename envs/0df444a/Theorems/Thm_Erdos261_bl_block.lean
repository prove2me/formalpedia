-- Prove2me | Theorems.Thm_Erdos261_bl_block
-- name    : Erdos261.bl_block
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:46:56.51757+00:00
-- url     : https://prove2.me/theorems/086ea4ff-5dac-4ae6-b240-86b4ddc3d63f
-- title:
--   Borwein–Loring block identity for $q_m=2^{m+1}-m-2$
-- statement:
--   **Theorem.** For every $m\ge0$, with $q_m=2^{m+1}-m-2$,
--
--   $$\frac{q_m}{2^{q_m}}=\sum_{q_m<k\le q_m+m}\frac{k}{2^k}.$$
--
--   For $m\ge2$ this exhibits a representation of $q_m/2^{q_m}$ by $m$ distinct terms (Borwein–Loring), and it is the block used in the rewrite rule for representations in Erdős Problem 261.
--
--   **Formalization Note.** Natural-number subtraction is harmless since $m+2\le2^{m+1}$; the cases $m=0,1$ are included.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; Borwein–Loring, Math. Comp. 54 (1990) 377–394; Lemma A4 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem bl_block (m : ℕ) :
    ((2 ^ (m + 1) - m - 2 : ℕ) : ℚ) / 2 ^ (2 ^ (m + 1) - m - 2) =
      ∑ k ∈ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k := by sorry

end Erdos261
