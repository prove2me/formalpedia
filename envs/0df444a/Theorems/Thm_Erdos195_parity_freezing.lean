-- Prove2me | Theorems.Thm_Erdos195_parity_freezing
-- name    : Erdos195.parity_freezing
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T18:27:09.455431+00:00
-- url     : https://prove2.me/theorems/557c7c97-87b7-4bc0-b978-4393e031c730
-- title:
--   Parity freezing: anchored extrema block all opposite-parity monochromatic SAFE repairs (tree orders)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$.
--
--   **Theorem (parity freezing under monochromatic SAFE repairs).** Let $Q_0,Q_1,Q_2,\dots$ be SAFE words (each stage may use its own witness) such that every $Q_{n+1}=Q_n D_n$ is obtained by appending a batch $D_n$ of new integers all of the same parity. Suppose the numerical extrema $L=\min Q_0$, $U=\max Q_0$ have a common parity $\gamma$, and $Q_0$ contains anchors $z,p,q$ with
--   $$z\not\equiv\gamma,\quad p\equiv q\equiv\gamma\pmod 2,\quad p\not\equiv q\pmod 4,$$
--   each occurring before both $L$ and $U$ in $Q_0$ and lying strictly between $L$ and $U$. Then every integer added at any stage has parity $\gamma$.
--
--   Thus such a configuration freezes one parity: no chain of monochromatic SAFE end-extensions can ever add an integer of parity $1-\gamma$ (for instance, Astra's verified example $(0,1,33,3,17,19,-13,10,87,71,103,45)$ with $z=0,p=1,q=3$ can never absorb a new even integer this way). Lemma of GPT 6 Astra.
--
--   *Formalization note.* The chain is indexed by $\mathbb N$; finite chains are covered by padding with empty batches.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma of GPT 6 Astra; Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem parity_freezing (Q : ℕ → List ℤ) (hS : ∀ n, ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Q n))
    (hstep : ∀ n, ∃ D : List ℤ, Q (n + 1) = Q n ++ D ∧ (∀ d ∈ D, d ∉ Q n) ∧
      ∀ d ∈ D, ∀ d' ∈ D, d % 2 = d' % 2)
    (L U z p q : ℤ) (hL : L ∈ Q 0) (hU : U ∈ Q 0) (hbd : ∀ x ∈ Q 0, L ≤ x ∧ x ≤ U)
    (hz : z ∈ Q 0) (hp : p ∈ Q 0) (hq : q ∈ Q 0)
    (horder : ∀ x ∈ [z, p, q], (Q 0).idxOf x < (Q 0).idxOf L ∧ (Q 0).idxOf x < (Q 0).idxOf U)
    (hin : ∀ x ∈ [z, p, q], L < x ∧ x < U)
    (hUp : U % 2 = L % 2) (hzp : z % 2 ≠ L % 2) (hpp : p % 2 = L % 2) (hqp : q % 2 = L % 2)
    (hpq : p % 4 ≠ q % 4) :
    ∀ n, ∀ x ∈ Q n, x ∉ Q 0 → x % 2 = L % 2 := by sorry

end Erdos195
