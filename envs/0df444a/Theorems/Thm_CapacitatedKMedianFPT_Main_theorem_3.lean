-- Prove2me | Theorems.Thm_CapacitatedKMedianFPT_Main_theorem_3
-- name    : CapacitatedKMedianFPT.Main.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:15:34.435717+00:00
-- url     : https://prove2.me/theorems/b1bb1fea-1a58-432a-8a86-5dd665b46d5a
-- title:
--   Theorem 3 — an m-perfect family of size 2^{O(m)} log|F| in time 2^{O(m)}|F| log|F|
-- statement:
--   For an integer $m\ge1$ and a finite set $F$, a family $\mathcal H$ of functions $F\to[m]$ is **$m$-perfect** if every $O\subseteq F$ with $|O|=m$ is colored injectively by some $h\in\mathcal H$, i.e. $|\{h(o):o\in O\}|=m$.
--
--   **Theorem (Alon–Yuster–Zwick).** An $m$-perfect family $\mathcal H_m$ of size $2^{O(m)}\log|F|$ can be constructed in time $2^{O(m)}|F|\log|F|$.
--
--   One program does this for all $m$ and $|F|$, with one absolute constant in both $O(m)$'s. The algorithm of Theorem 1 enumerates $\chi\in\mathcal H_k$ to make the facility groups disjoint.
--
--   **Formalization Note** The program receives $(m,N)$ with $F=\{0,\dots,N-1\}$, $N\ge1$, and writes the family as a table of colors $0,\dots,m-1$. Time is word-RAM time with the word length of the input; $\log|F|$ is $\log_2\max(2,N)$.
--
--   Differences from the source:
--
--   - encoding: constructed in time 2^O(m)|F| log|F| → one program of `Machine`, word-RAM time with the input's word length, ≤ 2^{cm}·N·log₂ max(2, N), c absolute; reason: the word RAM is the model of the cited construction; O(m) as one constant
--   - encoding: |F| arbitrary, log|F| → N = |F| ≥ 1 and log₂ max(2, N); reason: for |F| = 0 the bound 2^O(m)·0 cannot be met by any halting program, and log 1 = 0 likewise at |F| = 1; the hypothesis excludes only this degenerate case
--   - encoding: functions F → [m] → tables of colors 0, …, m−1 on F = {0, …, N−1}; reason: relabelling
-- source:
--   Aditya Anand, Yichen Huang, Ragesh Jaiswal, Amit Kumar, Euiwoong Lee, Jatin Yadav, A Tight FPT Approximation for Capacitated k-Median, STOC 2027 submission #1646 (October 2026), p. 6, Color coding and Theorem 3 ([AYZ95])

import Mathlib
import Definitions.Def_CapacitatedKMedianFPT_Main_Machine
import Definitions.Def_CapacitatedKMedianFPT_Main_Encoding

set_option autoImplicit false

namespace CapacitatedKMedianFPT.Main

/-- **Theorem 3** ([AYZ95]) (p. 6). One program, given `m ≥ 1` and `N = |F| ≥ 1`, outputs an
`m`-perfect family of functions `F → [m]` of size at most `2^{cm} log₂ max(2, N)`, within word-RAM
time `2^{cm} · N · log₂ max(2, N)` (word length that of the input), for one absolute constant `c`. -/
theorem theorem_3 :
    ∃ (A : Program) (c : ℕ), ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
      ∃ (mem : Memory) (s : Stats), RunsTo A zeroOracle [(m : ℚ), (N : ℚ)] mem s ∧
        (s.wordTime (wordSizeOf [(m : ℚ), (N : ℚ)]) : ℝ) ≤
          (2 : ℝ) ^ (c * m) * N * Real.logb 2 (max 2 (N : ℝ)) ∧
        IsPerfectFamilyOutput m N ((2 : ℝ) ^ (c * m) * Real.logb 2 (max 2 (N : ℝ))) mem := by sorry

end CapacitatedKMedianFPT.Main
