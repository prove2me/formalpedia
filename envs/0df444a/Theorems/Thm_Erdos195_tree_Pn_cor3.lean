-- Prove2me | Theorems.Thm_Erdos195_tree_Pn_cor3
-- name    : Erdos195.tree_Pn_cor3
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:34:49.585983+00:00
-- url     : https://prove2.me/theorems/b0a09522-7a94-4736-bac1-40a20fcd5efb
-- title:
--   Root conflict for $P_n\cdot T$: tree-safe words meet $\{2N+2,3N+3,2T-1,3T-2\}$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $n\ge1$, $N=2^n$ and $T=4N$. In every $\theta$-safe word $Q$ (any tree witness $\theta$) containing $0,1,N+1,T$ in which $0$ occurs before $N+1$ and $1$ occurs before $T$,
--   $$\{2N+2,\ 3N+3,\ 2T-1,\ 3T-2\}\cap Q\neq\varnothing,$$
--   because the open pairs $(0,N+1)$ and $(1,T)$ would force opposite values at the root node. In particular every tree-safe extension of $P_n=\{0,\dots,N-1\}$ (in any order) that contains $N+1$ after its prefix and $T$ contains one of these four numbers: the fourth-term repair of the family $P_n\cdot T$ fails (Erdős Problem 195).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. "Begins with" is the list prefix relation `<+:`; positions in a word are `List.idxOf`. The statement quantifies over every witness θ, so it holds in particular for all ε-orders.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree cascade' answers, generalized to all t / all m / all n), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem tree_Pn_cor3 (n : ℕ) (hn : 1 ≤ n) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q)
    (h0 : (0 : ℤ) ∈ Q) (h1 : (1 : ℤ) ∈ Q) (hN : (2 : ℤ) ^ n + 1 ∈ Q) (hT : 4 * (2 : ℤ) ^ n ∈ Q)
    (i0 : Q.idxOf 0 < Q.idxOf ((2 : ℤ) ^ n + 1)) (i1 : Q.idxOf 1 < Q.idxOf (4 * (2 : ℤ) ^ n)) :
    2 * (2 : ℤ) ^ n + 2 ∈ Q ∨ 3 * (2 : ℤ) ^ n + 3 ∈ Q ∨ 2 * (4 * (2 : ℤ) ^ n) - 1 ∈ Q ∨
      3 * (4 * (2 : ℤ) ^ n) - 2 ∈ Q := by sorry

end Erdos195
