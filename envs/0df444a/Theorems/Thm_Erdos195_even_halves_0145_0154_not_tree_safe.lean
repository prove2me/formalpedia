-- Prove2me | Theorems.Thm_Erdos195_even_halves_0145_0154_not_tree_safe
-- name    : Erdos195.even_halves_0145_0154_not_tree_safe
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-11-18T11:54:58.885849+00:00
-- url     : https://prove2.me/theorems/37648dcd-e3c5-4f0e-9e9b-a5fdae22cda0
-- title:
--   The even halves $(0,1,4,5)$ and $(0,1,5,4)$ of the $(1,5)$ reflection completion are not tree-safe
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1\Leftrightarrow\theta(k,\,x\bmod 2^k)=1$. A finite word $Q$ is $\theta$-safe if the completion “letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order” contains no monotone $4$-term arithmetic progression. Positions are first occurrences.
--
--   **Theorem.** Neither of the words $(0,1,4,5)$ and $(0,1,5,4)$ is tree-safe for any witness $\theta$.
--
--   These are the only two candidate even halves (after division by $2$) of a reflection completion of the safe odd word $(1,5)$, with even batches $E_1=\{0,2\}$ and $E_2=\{0,2,8,10\}$. In both words the in-order pairs $(0,1)$ and $(1,4)$ are open (the third and fourth terms $2,3$ and $7,10$ are absent). Both pairs occupy the root node $k=0$ and force opposite values of $\theta$ there: $\mathrm{bit}_0(1)=1$ while $\mathrm{bit}_0(4)=0$. The official criterion `exists_treeLt_safe_iff` therefore fails.
--
--   This is the exact limitation recorded in the finite reflection-completion analysis: reflection completion discharges all root and mixed-parity obligations, but batch ordering alone need not make the reflected even subsequence safe. The theorem does not claim that every even enlargement fails, does not preserve a prefix such as $(0,1,x)$, and does not settle Erdős #195.
--
--   **Formalization Note** Safety is official `Safe (treeLt θ)`. The two concrete words are `[0, 1, 4, 5]` and `[0, 1, 5, 4]`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); derived from analysis relayed by Ethan Cheung, hand-checked against the official Safe / treeLt / exists_treeLt_safe_iff definitions, Lean-verified.

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem even_halves_0145_0154_not_tree_safe :
    (¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 4, 5]) ∧
    (¬ ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [0, 1, 5, 4]) := by sorry

end Erdos195
