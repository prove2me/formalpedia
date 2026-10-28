-- Prove2me | Theorems.Thm_Erdos195_reverse_fourth_conflict
-- name    : Erdos195.reverse_fourth_conflict
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:12:28.182357+00:00
-- url     : https://prove2.me/theorems/64e87abc-29bc-4ed0-a9b2-a4b9bbbb62d6
-- title:
--   Reverse-order fourth term $3b-2a$ creates a node conflict
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. Let $P$ be a finite word and $a\neq b$ letters of $P$ with $b$ occurring before $a$. Put $c=3b-2a$ and suppose
--   $$c,\ 2a-b,\ 3a-2b,\ 6b-5a,\ 9b-8a\notin P.$$
--   Then the word $P\cdot c$ is not tree-safe. Indeed the in-order pairs $(b,a)$ and $(a,c)$ are then both open (neither continuation present), they sit at the same tree node $(k,\,a\bmod 2^k)$ with $k=\nu_2(b-a)$, and they force opposite bits there, since $\mathrm{bit}_k(c)=\mathrm{bit}_k(b)\neq\mathrm{bit}_k(a)$. This explains why the isolated-minimum completion by the fourth term $3b-2a$ has no analogue when the pair is taken in reverse order (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem reverse_fourth_conflict (P : List ℤ) (a b : ℤ) (ha : a ∈ P) (hb : b ∈ P)
    (hord : P.idxOf b < P.idxOf a) (hc : 3 * b - 2 * a ∉ P)
    (h1 : 2 * a - b ∉ P) (h2 : 3 * a - 2 * b ∉ P)
    (h3 : 6 * b - 5 * a ∉ P) (h4 : 9 * b - 8 * a ∉ P) :
    ¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (P ++ [3 * b - 2 * a]) := by sorry

end Erdos195
