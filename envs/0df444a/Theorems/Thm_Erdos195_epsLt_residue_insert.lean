-- Prove2me | Theorems.Thm_Erdos195_epsLt_residue_insert
-- name    : Erdos195.epsLt_residue_insert
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:52:13.032666+00:00
-- url     : https://prove2.me/theorems/764a9c18-c726-4f7c-8289-0b3117729bf7
-- title:
--   A safe word in one residue class mod $2^m$ absorbs any finite set outside it
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $P$ of distinct integers is $\varepsilon$-safe if the sequence "the letters of $P$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $m\ge 0$, $r\in\mathbb{Z}$, and let $P$ be an $\varepsilon$-safe word all of whose letters are $\equiv r \pmod{2^m}$. Define $\varepsilon'$ by $\varepsilon'_k = 1-\mathrm{bit}_k(r)$ for $k<m$ and $\varepsilon'_k=\varepsilon_k$ for $k\ge m$. Then every finite set $S$ of integers $\not\equiv r\pmod{2^m}$ can be listed as $s_1,\dots,s_n$ so that
--   $$s\prec_{\varepsilon'} p\ \ (s\in S,\ p\in P)\qquad\text{and}\qquad P\cdot s_1\cdots s_j\ \text{is } \varepsilon'\text{-safe for every } j.$$
--   In particular a word supported on a single residue class mod $2^m$ can absorb any finite set of targets outside that class (e.g. a word of even integers can absorb any finite set of odd integers), at the cost of changing only the first $m$ digits of $\varepsilon$. This is a step towards extension lemmas for constructing $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; $\varepsilon'$ is written as `fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k`; $S$ is a duplicate-free list and the ordering is a permutation `S'` of it; prefixes are `S'.take j`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_residue_insert (ε : ℕ → Bool) (m : ℕ) (r : ℤ) (P : List ℤ)
    (hS : Safe (epsLt ε) P) (hP : ∀ p ∈ P, (2 : ℤ) ^ m ∣ p - r)
    (S : List ℤ) (hSnd : S.Nodup) (hSr : ∀ s ∈ S, ¬ (2 : ℤ) ^ m ∣ s - r) :
    ∃ S' : List ℤ, S'.Perm S ∧
      (∀ s ∈ S, ∀ p ∈ P,
        epsLt (fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k) s p) ∧
      ∀ j : ℕ, Safe (epsLt (fun k => if k < m then decide (r / 2 ^ k % 2 = 0) else ε k))
        (P ++ S'.take j) := by sorry

end Erdos195
