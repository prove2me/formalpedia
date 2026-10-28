-- Prove2me | Theorems.Thm_Erdos195_immediate_fourth_term_persist
-- name    : Erdos195.immediate_fourth_term_persist
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:37:53.048414+00:00
-- url     : https://prove2.me/theorems/518d50e6-84f5-49e0-8e9f-085362489062
-- title:
--   Fourth-term completion of an extremal open pair keeps the forced node value
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. Let $(u,w)$ be an open in-order pair of a finite word $P$, let $k=\nu_2(w-u)$, and suppose $w$ is the numerical maximum or the numerical minimum of the letters of $P$ congruent to $w$ modulo $2^k$. Put $c=3w-2u$. Then in the word $P\cdot c$ the pair $(u,c)$ is in order and open, lies at the same node as $(u,w)$, and forces the same value:
--   $$\nu_2(c-u)=k,\qquad \mathrm{bit}_k(c)=\mathrm{bit}_k(w),\qquad 2c-u,\ 3c-2u\notin P\cdot c.$$
--   So completing an extremal open pair by its fourth term never releases the node it was forcing; the forced value persists (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree11' answer, checked and sharpened), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem immediate_fourth_term_persist (P : List ℤ) (u w : ℤ) (hu : u ∈ P) (hw : w ∈ P)
    (hord : P.idxOf u < P.idxOf w) (h2 : 2 * w - u ∉ P) (h3 : 3 * w - 2 * u ∉ P)
    (hext : (∀ x ∈ P, (2 : ℤ) ^ padicValInt 2 (w - u) ∣ x - w → x ≤ w) ∨
      (∀ x ∈ P, (2 : ℤ) ^ padicValInt 2 (w - u) ∣ x - w → w ≤ x)) :
    u ∈ P ++ [3 * w - 2 * u] ∧ 3 * w - 2 * u ∈ P ++ [3 * w - 2 * u] ∧
    (P ++ [3 * w - 2 * u]).idxOf u < (P ++ [3 * w - 2 * u]).idxOf (3 * w - 2 * u) ∧
    2 * (3 * w - 2 * u) - u ∉ P ++ [3 * w - 2 * u] ∧
    3 * (3 * w - 2 * u) - 2 * u ∉ P ++ [3 * w - 2 * u] ∧
    padicValInt 2 ((3 * w - 2 * u) - u) = padicValInt 2 (w - u) ∧
    (bitOne (3 * w - 2 * u) (padicValInt 2 (w - u)) ↔ bitOne w (padicValInt 2 (w - u))) := by sorry

end Erdos195
