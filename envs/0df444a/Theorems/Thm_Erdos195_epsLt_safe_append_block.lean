-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_append_block
-- name    : Erdos195.epsLt_safe_append_block
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:52:13.510754+00:00
-- url     : https://prove2.me/theorems/09393e0e-9fb7-4405-bae3-8b0cfe402427
-- title:
--   Appending a decreasing block below an $\varepsilon$-safe word
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $P$ of distinct integers is $\varepsilon$-safe if the sequence "the letters of $P$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $P$ be $\varepsilon$-safe and let $S=(s_1,\dots,s_n)$ be a list of integers not in $P$ such that
--   $$s\prec_\varepsilon p\ \ (s\in S,\ p\in P),\qquad s_j\prec_\varepsilon s_i\ \ (i<j),\qquad \forall a\text{ before }b\text{ in }P:\ 2b-a\in S\Rightarrow 3b-2a\in P.$$
--   Then for every $j$ the word $P\cdot s_1\cdots s_j$ is $\varepsilon$-safe. Thus an entire block of letters lying $\prec_\varepsilon$-below a safe word can be appended in decreasing order, provided no in-order pair of $P$ has its $3$-AP continuation in the block without its $4$-AP continuation in $P$. This is a step in Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195).
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; "$a$ before $b$" is `P.idxOf a < P.idxOf b`; decreasing order is `S.Pairwise (fun x y => epsLt ε y x)`; prefixes are `S.take j`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_append_block (ε : ℕ → Bool) (P S : List ℤ) (hS : Safe (epsLt ε) P)
    (hdisj : ∀ s ∈ S, s ∉ P) (hbelow : ∀ s ∈ S, ∀ p ∈ P, epsLt ε s p)
    (hdec : S.Pairwise (fun x y => epsLt ε y x))
    (hF : ∀ a ∈ P, ∀ b ∈ P, P.idxOf a < P.idxOf b → 2 * b - a ∈ S → 3 * b - 2 * a ∈ P) :
    ∀ j : ℕ, Safe (epsLt ε) (P ++ S.take j) := by sorry

end Erdos195
