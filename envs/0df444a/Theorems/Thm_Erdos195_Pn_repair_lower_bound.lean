-- Prove2me | Theorems.Thm_Erdos195_Pn_repair_lower_bound
-- name    : Erdos195.Pn_repair_lower_bound
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:38:04.114988+00:00
-- url     : https://prove2.me/theorems/b96176e5-f401-453a-961a-2cb87badf28d
-- title:
--   Tree-safe repair of $P_n\cdot T$ needs at least $n$ auxiliary letters
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $n\ge0$, $N=2^n$, $T=4N$. Let $Q$ be a $\theta$-safe word (any tree witness $\theta$) with $T\in Q$ and $N\notin Q$, such that for every $k<n$ the letters $N-2^{k+1}$, $N-2^k$, $2^k$ occur in $Q$, with $N-2^{k+1}$ before $N-2^k$ and $2^k$ before $T$. Then for every $k<n$
--   $$Q\cap\{N+2^k,\ 2T-2^k,\ 3T-2^{k+1}\}\neq\varnothing,\qquad\text{and}\qquad \#\{x\in Q:\ x\notin[0,N),\ x\neq T\}\ \ge\ n.$$
--   The hypotheses hold for every word that begins with $P_n=\{0,1,\dots,N-1\}$ listed in increasing $\prec_0$-order (the order with all digits preferred $0$) and contains $T$ but not $N$: the pairs $(N-2^{k+1},N-2^k)$ and $(2^k,T)$ sit at the same tree node $(k,0)$ and force opposite values there. So absorbing the single new target $T$ into $P_n$ by tree-safe insertion needs at least $n$ auxiliary letters: there is no uniform bound on the repair cost (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe` from `Definitions.Def_Erdos195_defs`; positions are `List.idxOf`; the count is the cardinality of `Q.toFinset` filtered by $x\notin[0,N)$, $x\ne T$. The word $P_n$ itself is not formalized; the theorem assumes only the order relations it uses.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statement from GPT 6 Astra (Oct 23 2026 'tree limits' answer, Thm 2), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem Pn_repair_lower_bound (n : ℕ) (θ : ℕ → ℤ → Bool) (Q : List ℤ)
    (hS : Safe (treeLt θ) Q) (hT : 4 * (2 : ℤ) ^ n ∈ Q) (hN : (2 : ℤ) ^ n ∉ Q)
    (hord : ∀ k < n, (2 : ℤ) ^ n - 2 ^ (k + 1) ∈ Q ∧ (2 : ℤ) ^ n - 2 ^ k ∈ Q ∧ (2 : ℤ) ^ k ∈ Q ∧
      Q.idxOf ((2 : ℤ) ^ n - 2 ^ (k + 1)) < Q.idxOf ((2 : ℤ) ^ n - 2 ^ k) ∧
      Q.idxOf ((2 : ℤ) ^ k) < Q.idxOf (4 * (2 : ℤ) ^ n)) :
    (∀ k < n, (2 : ℤ) ^ n + 2 ^ k ∈ Q ∨ 2 * (4 * (2 : ℤ) ^ n) - 2 ^ k ∈ Q ∨
      3 * (4 * (2 : ℤ) ^ n) - 2 ^ (k + 1) ∈ Q) ∧
    n ≤ (Q.toFinset.filter (fun x => ¬ (0 ≤ x ∧ x < (2 : ℤ) ^ n) ∧ x ≠ 4 * (2 : ℤ) ^ n)).card := by sorry

end Erdos195
