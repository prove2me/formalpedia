-- Prove2me | Theorems.Thm_Erdos195_shield_safe
-- name    : Erdos195.shield_safe
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T06:37:55.694657+00:00
-- url     : https://prove2.me/theorems/9f4e31eb-0c28-4d69-bd90-0b883712d6a5
-- title:
--   Shield lemma: $(u,w,6w-5u,3w-2u)$ is tree-safe and releases the node $N(u,w)$
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; it is tree-safe if it is $\theta$-safe for some $\theta$. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; an open pair lies at the node $N(a,b)=(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and $\theta$-safety requires $\theta(N(a,b))=\mathrm{bit}_k(b)$ there. For all integers $u\neq w$, the four-letter word
--   $$S(u,w)=(u,\ w,\ 6w-5u,\ 3w-2u)$$
--   is tree-safe, it closes the pair $(u,w)$ (its fourth term $3w-2u$ is present), and every open in-order pair $(a,b)$ of $S(u,w)$ lying at the node $N(u,w)$ forces the bit opposite to $\mathrm{bit}_k(w)$, $k=\nu_2(w-u)$. (Concretely, the open pairs are $(u,6w-5u)$, $(w,6w-5u)$, $(w,3w-2u)$, at levels $k+1$, $k$, $k+1$; for $(u,w)=(0,1)$ this is the word $(0,1,6,3)$.) Thus a 'shield' releases the value forced at $N(u,w)$ by the pair $(u,w)$: unlike the bare fourth-term completion, it flips the requirement at that node. This is a release lemma for two-letter prefixes in the tree-witness approach to Erdős Problem 195.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; `P ++ [c]` appends `c`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); statements from GPT 6 Astra (Oct 23 2026 'tree11' answer, checked and sharpened), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem shield_safe (u w : ℤ) (huw : u ≠ w) :
    (∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) [u, w, 6 * w - 5 * u, 3 * w - 2 * u]) ∧
    3 * w - 2 * u ∈ [u, w, 6 * w - 5 * u, 3 * w - 2 * u] ∧
    (∀ a b : ℤ, a ∈ [u, w, 6 * w - 5 * u, 3 * w - 2 * u] → b ∈ [u, w, 6 * w - 5 * u, 3 * w - 2 * u] →
      [u, w, 6 * w - 5 * u, 3 * w - 2 * u].idxOf a < [u, w, 6 * w - 5 * u, 3 * w - 2 * u].idxOf b →
      2 * b - a ∉ [u, w, 6 * w - 5 * u, 3 * w - 2 * u] →
      3 * b - 2 * a ∉ [u, w, 6 * w - 5 * u, 3 * w - 2 * u] →
      padicValInt 2 (b - a) = padicValInt 2 (w - u) →
      a % 2 ^ padicValInt 2 (w - u) = u % 2 ^ padicValInt 2 (w - u) →
      (bitOne b (padicValInt 2 (w - u)) ↔ ¬ bitOne w (padicValInt 2 (w - u)))) := by sorry

end Erdos195
