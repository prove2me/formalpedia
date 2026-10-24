-- Prove2me | Theorems.Thm_Erdos195_safe_affine_scale_iff
-- name    : Erdos195.safe_affine_scale_iff
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T12:41:07.141579+00:00
-- url     : https://prove2.me/theorems/1dde3004-ff98-4f1d-90e9-5b7a78144fe0
-- title:
--   Scaling $x\mapsto 2x+c$ transports tree safety to the shifted subtree witness, both directions
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1 \Leftrightarrow \theta(k,\,x\bmod 2^k)=1$ ($\mathrm{bit}_k$ is the $k$-th two's-complement binary digit). A finite word $Q$ of integers is $\theta$-safe if the completion "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression (positions of $a,a+r,a+2r,a+3r$ increasing, $r\neq0$). Positions in $Q$ are first occurrences. Let $c\in\{0,1\}$ and let $P$ be a finite word. Then the word $2P+c=(2p_1+c,2p_2+c,\dots)$ is $\theta$-safe if and only if $P$ is $\theta'$-safe, where $\theta'(k,r)=\theta(k+1,\,2r+c)$:
--
--   $$2P+c \text{ is } \theta\text{-safe} \iff P \text{ is } \theta(\cdot+1,\,2\cdot+c)\text{-safe}.$$
--
--   The forward direction transports a safe word on one parity class down to a safe word for the shifted subtree witness (e.g. $x\mapsto (x-1)/2$ on odd words), and the backward direction is the lifting: any safe word for any witness $\theta'$ lifts to a safe word on the class $c$ for every $\theta$ whose subtree at $c$ is $\theta'$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; self-similarity observation by GPT Sol (Oct 23 2026), general statements and Lean proofs by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem safe_affine_scale_iff (θ : ℕ → ℤ → Bool) (c : ℤ) (hc : c = 0 ∨ c = 1) (P : List ℤ) :
    Safe (treeLt θ) (P.map (fun y => 2 * y + c)) ↔
      Safe (treeLt (fun k r => θ (k + 1) (2 * r + c))) P := by sorry

end Erdos195
