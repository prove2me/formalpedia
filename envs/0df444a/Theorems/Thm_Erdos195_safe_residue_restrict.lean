-- Prove2me | Theorems.Thm_Erdos195_safe_residue_restrict
-- name    : Erdos195.safe_residue_restrict
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T12:41:13.164657+00:00
-- url     : https://prove2.me/theorems/e7dc8d81-0b47-40a4-909c-50ea1ccd18ee
-- title:
--   Residue-class subsequences of tree-safe words are tree-safe
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1 \Leftrightarrow \theta(k,\,x\bmod 2^k)=1$ ($\mathrm{bit}_k$ is the $k$-th two's-complement binary digit). A finite word $Q$ of integers is $\theta$-safe if the completion "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression (positions of $a,a+r,a+2r,a+3r$ increasing, $r\neq0$). Positions in $Q$ are first occurrences. For every modulus $m$ and residue $c$: if $Q$ is $\theta$-safe, then the subsequence of letters $x$ of $Q$ with $x\bmod m=c$ is again $\theta$-safe (for the same $\theta$).
--
--   $$Q\ \theta\text{-safe} \implies Q|_{\{x\,:\,x\equiv c \ (\mathrm{mod}\ m)\}}\ \theta\text{-safe}.$$
--
--   The reason is that a residue class is closed under $(a,b)\mapsto 2b-a$ and $(a,b)\mapsto 3b-2a$, so open pairs and in-order $3$-APs inside the class are unchanged. In particular the odd (or even) subsequence of a safe word is safe.
--
--   Formalization note: Lean `%` is `Int.emod`; the statement holds for all integers $m,c$ (trivially if the class is empty).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; self-similarity observation by GPT Sol (Oct 23 2026), general statements and Lean proofs by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem safe_residue_restrict (θ : ℕ → ℤ → Bool) (Q : List ℤ) (m c : ℤ) (hS : Safe (treeLt θ) Q) :
    Safe (treeLt θ) (Q.filter (fun x => decide (x % m = c))) := by sorry

end Erdos195
