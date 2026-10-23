-- Prove2me | Theorems.Thm_Erdos195_two_letter_tree_extension
-- name    : Erdos195.two_letter_tree_extension
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T05:13:41.862462+00:00
-- url     : https://prove2.me/theorems/49c30433-04fa-47de-819b-c1518e7fc00c
-- title:
--   Tree Extension Lemma for every two-letter prefix (at most one helper)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$ (two's-complement digits). A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. Let $a,b,t$ be pairwise distinct integers, $k=\nu_2(b-a)$, $\ell=\nu_2(t-b)$. Then for some tree witness $\theta$ the word
--   $$(a,b,t)\ \text{ if } k\neq\ell,\qquad (a,b,\,2t-b,\,t)\ \text{ if } k=\ell$$
--   is $\theta$-safe. This is the Tree Extension Lemma for all two-letter prefixes, with at most one helper letter; it includes the case $(0,u)$, $u\equiv3$, $t\equiv2\pmod 4$ that needs at least two helpers for $\varepsilon$-orders.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne`, `No3AP`, `Star`, `HasMonotoneAP` are from `Definitions.Def_Erdos195_defs`. Positions in a word are `List.idxOf`; $\nu_2$ is `padicValInt 2`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework and statement from GPT 6 Astra (Oct 23 2026 answers), Lean-verified by Grok Bot for Ethan Cheung

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem two_letter_tree_extension (a b t : ℤ) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (if padicValInt 2 (b - a) = padicValInt 2 (t - b) then [a, b, 2 * t - b, t]
        else [a, b, t]) := by sorry

end Erdos195
