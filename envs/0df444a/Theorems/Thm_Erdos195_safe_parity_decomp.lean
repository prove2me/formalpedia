-- Prove2me | Theorems.Thm_Erdos195_safe_parity_decomp
-- name    : Erdos195.safe_parity_decomp
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T12:41:09.35082+00:00
-- url     : https://prove2.me/theorems/fa94b062-80d4-43a6-b7b3-88df0e547d7c
-- title:
--   Parity decomposition of tree-witness safety (two half-scale problems plus a root condition)
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1 \Leftrightarrow \theta(k,\,x\bmod 2^k)=1$ ($\mathrm{bit}_k$ is the $k$-th two's-complement binary digit). A finite word $Q$ of integers is $\theta$-safe if the completion "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression (positions of $a,a+r,a+2r,a+3r$ increasing, $r\neq0$). Positions in $Q$ are first occurrences. For a word $Q$ let $Q_0$ be the subsequence of even letters mapped by $x\mapsto x/2$, and $Q_1$ the subsequence of odd letters mapped by $x\mapsto (x-1)/2$. Let $\theta_c(k,r)=\theta(k+1,\,2r+c)$ for $c\in\{0,1\}$. Then
--
--   $$Q \text{ is } \theta\text{-safe} \iff Q_0 \text{ is } \theta_0\text{-safe},\ Q_1 \text{ is } \theta_1\text{-safe, and (R) holds},$$
--
--   where the root condition (R) says: for every pair $a,b\in Q$ with $b-a$ odd and $a$ before $b$, (i) if $2b-a\in Q$ occurs after $b$ then $3b-2a\in Q$ occurs before $2b-a$; (ii) if neither $2b-a$ nor $3b-2a$ lies in $Q$ then $b$ is odd exactly when $\theta(0,0)=1$.
--
--   This is the exact self-similarity of tree safety: all non-root constraints split into two independent problems of the same kind one binary digit lower (for the two subtrees of $\theta$), and the halves interact only through the odd-difference root condition (R). It generalizes the parity decomposition for $\varepsilon$-orders (the case $\theta(k,r)=\varepsilon_k$).
--
--   Formalization note: `treeLt`, `Safe`, `bitOne` from `Definitions.Def_Erdos195_tree`/`Def_Erdos195_defs`; positions are `List.idxOf`; `x / 2` is floor division, so it equals $(x-1)/2$ on odd $x$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; self-similarity observation by GPT Sol (Oct 23 2026), general statements and Lean proofs by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem safe_parity_decomp (θ : ℕ → ℤ → Bool) (Q : List ℤ) :
    Safe (treeLt θ) Q ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
          ((Q.filter (fun x => decide (x % 2 = 0))).map (· / 2)) ∧
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
          ((Q.filter (fun x => decide (x % 2 = 1))).map (· / 2)) ∧
      (∀ a b : ℤ, a ∈ Q → b ∈ Q → (b - a) % 2 = 1 → Q.idxOf a < Q.idxOf b →
        (2 * b - a ∈ Q → Q.idxOf b < Q.idxOf (2 * b - a) →
          3 * b - 2 * a ∈ Q ∧ Q.idxOf (3 * b - 2 * a) < Q.idxOf (2 * b - a)) ∧
        (2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → (θ 0 0 = true ↔ b % 2 = 1))) := by sorry

end Erdos195
