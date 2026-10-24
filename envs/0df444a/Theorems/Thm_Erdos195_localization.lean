-- Prove2me | Theorems.Thm_Erdos195_localization
-- name    : Erdos195.localization
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T14:39:32.6956+00:00
-- url     : https://prove2.me/theorems/adf85ebf-e2d6-4d53-a094-cf18efac2cdb
-- title:
--   Localization: a safe extension inside one residue class lifts to the whole tree-safe word
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; $Q$ is SAFE if it is $\theta$-safe for some $\theta$. For letters $x$ before $z$ in $Q$, the pair $(x,z)$ is OPEN if neither $2z-x$ nor $3z-2x$ occurs in $Q$; it sits at the node $(h,\,x\bmod 2^h)$, $h=\nu_2(z-x)$, and forces the digit $\mathrm{bit}_h(z)$ there.
--
--   **Theorem (localization).** Let $Q$ be SAFE, fix a residue class $C=\rho+2^k\mathbb Z$, and let $D$ be a finite word of letters of $C$ none of which occurs in $Q$. Let $Q_C$ be the subsequence of $Q$ consisting of its letters in $C$. Assume
--   1. the local word $Q_C\cdot D$ is SAFE, and
--   2. (ancestor compatibility) every OPEN pair $(x,z)$ of $Q$ sitting at an ancestor node $(h,\rho\bmod 2^h)$ with $h<k$ forces $\mathrm{bit}_h(z)=\mathrm{bit}_h(\rho)$.
--
--   Then
--   $$Q\cdot D \text{ is SAFE.}$$
--   So a finite safe extension built locally inside one residue class transfers to the whole word, and no new conflict appears at a node shallower than $k$. Combined with local absorption recipes (one or two local letters, or a one-grandchild block), it gives target-last absorption inside arbitrary larger safe words.
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. $Q_C$ is `Q.filter (fun x => decide (x % 2 ^ k = ρ % 2 ^ k))`, and positions are `List.idxOf`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma and argument by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem localization (Q D : List ℤ) (k : ℕ) (ρ : ℤ)
    (hQ : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) Q)
    (hD : ∀ d ∈ D, d % 2 ^ k = ρ % 2 ^ k) (hDQ : ∀ d ∈ D, d ∉ Q)
    (hloc : ∃ θ : ℕ → ℤ → Bool,
      Safe (treeLt θ) (Q.filter (fun x => decide (x % 2 ^ k = ρ % 2 ^ k)) ++ D))
    (hC : ∀ x z : ℤ, x ∈ Q → z ∈ Q → Q.idxOf x < Q.idxOf z → 2 * z - x ∉ Q → 3 * z - 2 * x ∉ Q →
      padicValInt 2 (z - x) < k → x % 2 ^ padicValInt 2 (z - x) = ρ % 2 ^ padicValInt 2 (z - x) →
      (bitOne z (padicValInt 2 (z - x)) ↔ bitOne ρ (padicValInt 2 (z - x)))) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (Q ++ D) := by sorry

end Erdos195
