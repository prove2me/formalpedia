-- Prove2me | Theorems.Thm_ApproxPolySatCH_Main_randomized_turing_in_ch
-- name    : ApproxPolySatCH.Main.randomized_turing_in_ch
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:23.429735+00:00
-- url     : https://prove2.me/theorems/eb8ef24d-8753-4843-bcb1-98ac17b40bbf
-- title:
--   Randomized oracle reductions preserve membership in CH
-- statement:
--   Let $A$ and $L$ be binary languages. If $A$ belongs to the counting hierarchy and there is a polynomial-time randomized Turing reduction from $L$ to $A$, with two-sided error at most $1/3$ and a common polynomial clock on every branch, then $L$ also belongs to the counting hierarchy.
--
--   This is the oracle-closure step used in the proof of Theorem 1. In particular, if $A\in C_jP$, the randomized computation places $L$ in $\mathrm{BPP}^A\subseteq\mathrm{PP}^A\subseteq C_{j+1}P$. All machines, clocks and seed lengths are fixed uniformly before the input.
-- source:
--   Nikhil Balaji, Mahsa Shirmohammadi, Sébastien Tavenas, James Worrell, STOC 2027 submission #1125 (October 2026), proof of Theorem 1, p.26: APS_k ∈ BPP^A ⊆ PP^A ⊆ C_{j+1}P ⊆ CH; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1125.pdf#page=26

import Definitions.Def_ApproxPolySatCH_Main_ResultantLanguages

set_option autoImplicit false

namespace ApproxPolySatCH.Main

/-- The counting hierarchy is closed under two-sided-error randomized polynomial-time Turing reductions. -/
theorem randomized_turing_in_ch {A L : Language} (hA : InCH A)
    (hred : RandomizedTuringReduction L A) : InCH L := by sorry
