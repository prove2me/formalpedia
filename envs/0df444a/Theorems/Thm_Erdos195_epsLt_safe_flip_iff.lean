-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_flip_iff
-- name    : Erdos195.epsLt_safe_flip_iff
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T04:34:57.186833+00:00
-- url     : https://prove2.me/theorems/a3f5e76f-eae8-4e0a-8325-2e73eea19522
-- title:
--   Bit-flip symmetry: $Q$ is $\varepsilon$-safe iff $-1-Q$ is $(1-\varepsilon)$-safe
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic total order on $\mathbb{Z}$ given by $x\prec_\varepsilon y$ iff $x\neq y$ and the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, where $k=\nu_2(y-x)$. A finite word $Q$ of integers is $\varepsilon$-safe if the sequence \"the letters of $Q$ in order, then all remaining integers in $\prec_\varepsilon$-order\" contains no monotone $4$-term arithmetic progression. Let $\sigma(x)=-1-x$ and let $\bar\varepsilon_k=1-\varepsilon_k$ be the complementary digit sequence. Then $Q$ is $\varepsilon$-safe if and only if the word $\sigma(Q)$ (apply $\sigma$ letterwise) is $\bar\varepsilon$-safe.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (statement suggested by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_flip_iff (ε : ℕ → Bool) (Q : List ℤ) :
    Safe (epsLt ε) Q ↔ Safe (epsLt (fun k => !ε k)) (Q.map (fun x => -1 - x)) := by sorry

end Erdos195
