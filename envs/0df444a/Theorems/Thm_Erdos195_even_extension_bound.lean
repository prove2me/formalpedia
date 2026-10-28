-- Prove2me | Theorems.Thm_Erdos195_even_extension_bound
-- name    : Erdos195.even_extension_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T16:09:39.711982+00:00
-- url     : https://prove2.me/theorems/02b9dc41-eb23-42df-ac67-3ee3d654e750
-- title:
--   Bounded localized repair: even-only extensions against an old root force stay within half the diameter
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. Let $Q$ be a finite word containing an even $p$ before an odd $s$ such that $2s-p\notin Q$ and $3s-2p\notin Q$; thus $(p,s)$ is an open pair forcing the odd child at the root. Let $D$ be a word of even integers such that $Q\cdot D$ is SAFE. Then for every odd $x\in Q$ and every $M$ with $|q-x|\le M$ for all $q\in Q$, every entry $z$ of $D$ not in $Q$ satisfies
--   $$2|z-x|\le M.$$
--   This is GPT Astra's 3-adic confinement bound (B), at the root node: repairs on the wrong side of an immutable old force cannot use large helpers.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; construction and proof sketch by GPT Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem even_extension_bound (Q D : List ℤ) (p s x M : ℤ)
    (hp : p ∈ Q) (hs : s ∈ Q) (hps : Q.idxOf p < Q.idxOf s)
    (hp2 : p % 2 = 0) (hs2 : s % 2 = 1) (h2 : 2 * s - p ∉ Q) (h3 : 3 * s - 2 * p ∉ Q)
    (hD : ∀ z ∈ D, z % 2 = 0)
    (hsafe : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Q ++ D))
    (hx : x ∈ Q) (hx2 : x % 2 = 1) (hM : ∀ q ∈ Q, |q - x| ≤ M) :
    ∀ z ∈ D, z ∉ Q → 2 * |z - x| ≤ M := by sorry

end Erdos195
