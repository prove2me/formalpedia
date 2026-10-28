-- Prove2me | Theorems.Thm_Erdos195_odd_entry_demand
-- name    : Erdos195.odd_entry_demand
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T08:10:13.276898+00:00
-- url     : https://prove2.me/theorems/c589731c-4954-4d63-93ef-8000c798fbf6
-- title:
--   Odd-entry demand for root-releasing tree-safe words starting with 0
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. Let $Q$ be a $\theta$-safe word whose first letter is $0$ and which is a true root release. Then for every odd letter $z$ of $Q$:
--   $$2z\in Q\ \text{or}\ 3z\in Q,\qquad\text{and}\qquad 3z\notin Q\implies 2z\in Q\ \text{occurs before}\ z.$$
--   Moreover, if $Q$ has an odd letter, then some odd letter $z$ is grounded: $3z\notin Q$ and $2z$ occurs before $z$. Thus every odd letter starts a forced chain $z, 3z, 9z,\dots$ that must end at a grounded letter whose double is placed earlier; this is the basic necessary condition for releasing the root after a prefix, e.g. after $(0,1,x)$ the letters $3$ and $3x$ are forced (Erdős Problem 195, tree-witness approach).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; "starts with 0" is `Q.head? = some 0`; the release hypothesis is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework, statements by Grok Bot for Ethan Cheung (hand reasoning, Oct 23 2026), Lean-verified

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem odd_entry_demand (θ : ℕ → ℤ → Bool) (Q : List ℤ) (hS : Safe (treeLt θ) Q)
    (h0 : Q.head? = some 0)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0) :
    (∀ z ∈ Q, z % 2 = 1 →
      (2 * z ∈ Q ∨ 3 * z ∈ Q) ∧ (3 * z ∉ Q → 2 * z ∈ Q ∧ Q.idxOf (2 * z) < Q.idxOf z)) ∧
    ((∃ z ∈ Q, z % 2 = 1) →
      ∃ z ∈ Q, z % 2 = 1 ∧ 3 * z ∉ Q ∧ 2 * z ∈ Q ∧ Q.idxOf (2 * z) < Q.idxOf z) := by sorry

end Erdos195
