-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_parity_decomp
-- name    : Erdos195.epsLt_safe_parity_decomp
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T02:58:50.214766+00:00
-- url     : https://prove2.me/theorems/f9f65ed3-9844-43c6-95be-dcd2cf7368d5
-- title:
--   Parity decomposition of $\varepsilon$-safety
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order" contains no monotone $4$-term arithmetic progression. Let $\eta_k=\varepsilon_{k+1}$, and for $p\in\{0,1\}$ let $R_p$ be the word obtained from $Q$ by keeping the letters $x\equiv p\pmod 2$, in order, and replacing each by $(x-p)/2$. Then $Q$ is $\varepsilon$-safe if and only if all of the following hold:
--   $$\begin{aligned}&(1)\ R_0\text{ and }R_1\text{ are }\eta\text{-safe};\\ &(2)\ Q\text{ contains no in-order }4\text{-AP }a,a+r,a+2r,a+3r\text{ with }r\text{ odd};\\ &(3)\ \text{if }r\text{ is odd and }a,a+r,a+2r\text{ occur in this order in }Q,\text{ then }a+3r\in Q;\\ &(4)\ \text{if }a\text{ precedes }b\text{ in }Q,\ b-a\text{ odd},\ 2b-a\notin Q,\ 3b-2a\notin Q,\text{ then }b\equiv\varepsilon_0\pmod 2.\end{aligned}$$
--   So safety splits into the two parity classes (a problem of the same kind one binary digit lower) plus cross-parity conditions that involve only $\varepsilon_0$. This reduces extension and merging questions for Ho-style constructions of $4$-AP-free permutations of $\mathbb{Z}$ (Erdős Problem 195) to the rescaled parity classes.
--
--   Formalization note: `Safe`, `epsLt` are from `Definitions.Def_Erdos195_defs`; $R_0$ is `(Q.filter (fun x => decide (x % 2 = 0))).map (fun x => x / 2)`, $R_1$ is the analogue with `(x - 1) / 2`; "precedes" is comparison of `List.idxOf`; condition (4) is stated as `b % 2 = 1 ↔ ε 0 = true`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_parity_decomp (ε : ℕ → Bool) (Q : List ℤ) :
    Safe (epsLt ε) Q ↔
      Safe (epsLt (fun k => ε (k + 1))) ((Q.filter (fun x => decide (x % 2 = 0))).map (fun x => x / 2)) ∧
      Safe (epsLt (fun k => ε (k + 1)))
        ((Q.filter (fun x => decide (x % 2 = 1))).map (fun x => (x - 1) / 2)) ∧
      (∀ a r : ℤ, r % 2 = 1 → a ∈ Q → a + r ∈ Q → a + 2 * r ∈ Q → a + 3 * r ∈ Q →
        Q.idxOf a < Q.idxOf (a + r) → Q.idxOf (a + r) < Q.idxOf (a + 2 * r) →
        ¬ Q.idxOf (a + 2 * r) < Q.idxOf (a + 3 * r)) ∧
      (∀ a r : ℤ, r % 2 = 1 → a ∈ Q → a + r ∈ Q → a + 2 * r ∈ Q →
        Q.idxOf a < Q.idxOf (a + r) → Q.idxOf (a + r) < Q.idxOf (a + 2 * r) → a + 3 * r ∈ Q) ∧
      (∀ a ∈ Q, ∀ b ∈ Q, Q.idxOf a < Q.idxOf b → (b - a) % 2 = 1 →
        2 * b - a ∉ Q → 3 * b - 2 * a ∉ Q → (b % 2 = 1 ↔ ε 0 = true)) := by sorry

end Erdos195
