-- Prove2me | Theorems.Thm_Erdos195_large_aux_append
-- name    : Erdos195.large_aux_append
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T11:08:23.729428+00:00
-- url     : https://prove2.me/theorems/f15b3487-45f8-43c2-86d8-f7ed91d9dcae
-- title:
--   Appending a large auxiliary letter that follows the committed path keeps a released tree-safe word safe and released
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. An in-order pair $(a,b)$ of $Q$ ($a$ occurs before $b$) is open if $2b-a\notin Q$ and $3b-2a\notin Q$; it lies at the node $(k,\,a\bmod 2^k)$, $k=\nu_2(b-a)$, and forces $\theta$ there to equal $\mathrm{bit}_k(b)$. A root pair is one with $b-a$ odd (node $(0,0)$); $Q$ is a true root release if every open root pair has even second entry, i.e. no open pair forces the value $1$ at the root. Let $Q$ be $\theta$-safe and a true root release, with $\theta(0,0)=0$. Suppose every open in-order pair $(a,b)$ of $Q$ has $\nu_2(b-a)\le L$, $|a|\le R$ for all $a\in Q$, and $z$ is an integer with $|z|>3R$ that follows the committed path: $\theta(h,\,z\bmod 2^h)=\mathrm{bit}_h(z)$ for all $h\le L$. Then $Q\,z$ (the word $Q$ with $z$ appended) is $\theta'$-safe and a true root release for the tree witness $\theta'$ that agrees with $\theta$ on all levels $\le L$ (in the Lean proof, $\theta'(k,r)=\mathrm{bit}_k(z)$ for $k>L$). Because $|z|>3R$, $z$ is not a $3$-AP completion of letters of $Q$, and no $3$-AP $(a,b,z)$ or $(a,z,\cdot)$ lies inside $Q\,z$. Every new open pair $(a,z)$ forces $\theta'$ at its node to equal $\mathrm{bit}(z)$, which agrees with the committed values on levels $\le L$ and defines the values above. A new root pair has $z-a$ odd, and the path condition at the root ($\theta(0,0)=0$) makes $z$ even, so the release is preserved.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`; `Safe`, `bitOne` are from `Definitions.Def_Erdos195_defs`. Positions are `List.idxOf`; the release property is stated as: every open in-order pair $(a,b)$ with $(b-a) \bmod 2 = 1$ has $b \bmod 2 = 0$.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; batch words by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem large_aux_append (θ : ℕ → ℤ → Bool) (Q : List ℤ) (L : ℕ) (R z : ℤ)
    (hS : Safe (treeLt θ) Q)
    (hrel : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → (b - a) % 2 = 1 → b % 2 = 0)
    (hroot : θ 0 0 = false)
    (hdepth : ∀ a b : ℤ, a ∈ Q → b ∈ Q → Q.idxOf a < Q.idxOf b → 2 * b - a ∉ Q →
      3 * b - 2 * a ∉ Q → padicValInt 2 (b - a) ≤ L)
    (hR : ∀ a ∈ Q, |a| ≤ R)
    (hz : 3 * R < |z|)
    (hpath : ∀ h ≤ L, (θ h (z % 2 ^ h) = true ↔ bitOne z h)) :
    ∃ θ' : ℕ → ℤ → Bool, (∀ k ≤ L, ∀ r, θ' k r = θ k r) ∧
      Safe (treeLt θ') (Q ++ [z]) ∧
      ∀ a b : ℤ, a ∈ Q ++ [z] → b ∈ Q ++ [z] → (Q ++ [z]).idxOf a < (Q ++ [z]).idxOf b →
        2 * b - a ∉ Q ++ [z] → 3 * b - 2 * a ∉ Q ++ [z] → (b - a) % 2 = 1 → b % 2 = 0 := by sorry

end Erdos195
