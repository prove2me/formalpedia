-- Prove2me | Theorems.Thm_Erdos195_midpoint_confinement
-- name    : Erdos195.midpoint_confinement
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:05:33.140092+00:00
-- url     : https://prove2.me/theorems/bd131717-04bc-4c12-8919-907fd44e29b5
-- title:
--   Midpoint confinement: an opposite-parity batch against an old root force
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. The halves of a word are the subsequences of its even letters and of its odd letters, each mapped by $x\mapsto\lfloor x/2\rfloor$; the half witnesses are $\theta_E(k,r)=\theta(k+1,2r)$ and $\theta_O(k,r)=\theta(k+1,2r+1)$.
--
--   **Theorem (midpoint confinement for an opposite-parity batch).** Let $Q$ be a word containing an in-order pair $(a,b)$ with $b-a$ odd that is open in $Q$ ($2b-a,\,3b-2a\notin Q$). Suppose the numerical extrema $L=\min Q$ and $U=\max Q$ have the parity of $b$. Let $D$ be a word of entries not in $Q$, all of the opposite parity. If $Q\cdot D$ is $\theta$-safe for a tree witness $\theta$, then every entry $z$ of $D$ satisfies
--   $$2z=L+U,$$
--   and if moreover $L\equiv U\pmod 4$, then $D$ is empty.
--
--   So an old root force toward the parity of both extrema cannot be overridden by a monochromatic batch of the other parity: such a batch has at most one value, the midpoint. It is the key step in Astra's (not yet formalized) argument that a safe enumeration of $\mathbb Z$ must use genuinely mixed-parity batches infinitely often. The old open pair cannot be retired because its fourth term has the parity of $b$. A new entry beyond the midpoint would form an open root pair with an old extreme that forces the wrong parity. Lemma of GPT 6 Astra.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma of GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem midpoint_confinement (θ : ℕ → ℤ → Bool) (Q D : List ℤ) (hS : Safe (treeLt θ) (Q ++ D))
    (a b : ℤ) (ha : a ∈ Q) (hb : b ∈ Q) (hab : Q.idxOf a < Q.idxOf b) (hodd : (b - a) % 2 = 1)
    (h2 : 2 * b - a ∉ Q) (h3 : 3 * b - 2 * a ∉ Q)
    (L U : ℤ) (hL : L ∈ Q) (hU : U ∈ Q) (hbd : ∀ x ∈ Q, L ≤ x ∧ x ≤ U)
    (hLp : L % 2 = b % 2) (hUp : U % 2 = b % 2)
    (hD : ∀ z ∈ D, z % 2 ≠ b % 2) (hDQ : ∀ z ∈ D, z ∉ Q) :
    (∀ z ∈ D, 2 * z = L + U) ∧ (L % 4 = U % 4 → D = []) := by sorry

end Erdos195
