-- Prove2me | Theorems.Thm_Erdos261_no_second_phase_dioph
-- name    : Erdos261.no_second_phase_dioph
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T19:08:12.20407+00:00
-- url     : https://prove2.me/theorems/438eb0e7-4fc3-40cb-8739-0eb6681033c0
-- title:
--   The equation $r(2^{t+1}-1)=2^{j+1}+t-1$ has no solutions with $t\ge1$
-- statement:
--   **Theorem.** For all integers $j,r\ge0$ and $t\ge1$,
--
--   $$r\,(2^{t+1}-1)\ne 2^{j+1}+t-1.$$
--
--   With $M=2^{t+1}-1$ one has $2^{j+1}\equiv 2^e\pmod M$ for $e=(j+1)\bmod (t+1)\le t$, and $1\le 2^e+t-1<M$, so $M\nmid 2^{j+1}+t-1$. In Erdős Problem 261 this equation describes greedy termination right after the first doubling phase (see `no_two_phase_termination`).
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); greedy carry as in Borwein–Loring 1990 / Tengely–Ulas–Zygadło 2020 (platform def Def_Erdos261_defs); Claim A2 of claim from GPT 6.1 Sol (second answer, Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem no_second_phase_dioph (j r t : ℕ) (ht : 1 ≤ t) : r * (2 ^ (t + 1) - 1) ≠ 2 ^ (j + 1) + t - 1 := by sorry

end Erdos261
