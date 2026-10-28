-- Prove2me | Theorems.Thm_Erdos195_iterated_isolated_min
-- name    : Erdos195.iterated_isolated_min
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T06:12:23.26167+00:00
-- url     : https://prove2.me/theorems/249fbea6-562a-406e-9c95-59669c9141b0
-- title:
--   Iterated isolated-minimum completions along $a+(2^i-1)(b-a)$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. Let $P$ be $\theta$-safe, $a\neq b$, $r=b-a$, $k=\nu_2(r)$ and $x_i=a+(2^i-1)r$ (so $x_0=a$, $x_1=b$, $x_{i+2}=3x_{i+1}-2x_i$). Put $Q_n=P\cdot(x_2,\dots,x_{n+1})$. Assume $b\in P$ is the $\theta$-minimum of $P$, $b$ is alone in its class mod $2^{k+1}$ among the letters of $P$, and for every $n$ the number $x_{n+2}$ is not $2v-u$ for any $u$ occurring before $v$ in $Q_n$. Then for every $n\ge0$ there is a tree witness $\theta_n$ such that
--   $$Q_n\ \text{is}\ \theta_n\text{-safe},\quad x_{n+1}\ \text{is the}\ \theta_n\text{-minimum of}\ Q_n,\quad x_{n+1}\ \text{is alone in its class mod}\ 2^{k+n+1}.$$
--   So the isolated-minimum completion can be iterated indefinitely along the doubling sequence (Erdős Problem 195).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree' answers tree10, generalized), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem iterated_isolated_min (θ : ℕ → ℤ → Bool) (P : List ℤ) (a b : ℤ)
    (hP : Safe (treeLt θ) P) (hb : b ∈ P) (hab : a ≠ b)
    (hmin : ∀ x ∈ P, x ≠ b → treeLt θ b x)
    (hiso : ∀ x ∈ P, x ≠ b → ¬ (2 : ℤ) ^ (padicValInt 2 (b - a) + 1) ∣ x - b)
    (hno : ∀ (n : ℕ) (u v : ℤ),
      u ∈ P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a)) →
      v ∈ P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a)) →
      (P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a))).idxOf u <
        (P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a))).idxOf v →
      a + (2 ^ (n + 2) - 1) * (b - a) ≠ 2 * v - u) :
    ∀ n : ℕ, ∃ θ' : ℕ → ℤ → Bool,
      Safe (treeLt θ') (P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a))) ∧
      a + (2 ^ (n + 1) - 1) * (b - a) ∈
        P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a)) ∧
      (∀ y ∈ P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a)),
        y ≠ a + (2 ^ (n + 1) - 1) * (b - a) → treeLt θ' (a + (2 ^ (n + 1) - 1) * (b - a)) y) ∧
      (∀ y ∈ P ++ (List.range n).map (fun j => a + (2 ^ (j + 2) - 1) * (b - a)),
        y ≠ a + (2 ^ (n + 1) - 1) * (b - a) →
        ¬ (2 : ℤ) ^ (padicValInt 2 (b - a) + n + 1) ∣ y - (a + (2 ^ (n + 1) - 1) * (b - a))) := by sorry

end Erdos195
