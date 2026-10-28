-- Prove2me | Theorems.Thm_Erdos195_block_reflection_absorption
-- name    : Erdos195.block_reflection_absorption
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T14:33:38.252825+00:00
-- url     : https://prove2.me/theorems/3779d9fd-1d7f-46e0-9b59-9122e8a0f072
-- title:
--   Reflection absorption for a one-grandchild block: $(a,B,2y-B,y)$ is tree-safe
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression; $Q$ is SAFE if it is $\theta$-safe for some $\theta$.
--
--   **Theorem (reflection absorption for a one-grandchild block).** Let $a\in\mathbb Z$, $k\ge 0$, and let $B=(b_1,\dots,b_m)$ be a finite word such that $a\cdot B$ is SAFE. Suppose that
--   - $\nu_2(b-a)=k$ for every $b\in B$ (so $a$ and $B$ lie in the same class mod $2^k$ but in opposite classes mod $2^{k+1}$),
--   - all entries of $B$ are congruent modulo $2^{k+2}$ (one grandchild), and
--   - $y\ne a$ and $y\equiv a \pmod{2^{k+1}}$.
--
--   Then the word
--   $$\bigl(a,\ b_1,\dots,b_m,\ 2y-b_1,\dots,2y-b_m,\ y\bigr)$$
--   is SAFE. Thus the target $y$ is absorbed last, using exactly $|B|$ auxiliary letters (the reflection of $B$ about $y$, in the original order).
--
--   Formalization note: `treeLt θ` is from `Definitions.Def_Erdos195_tree`, and `Safe` is from `Definitions.Def_Erdos195_defs`. The hypotheses are stated with divisibility: $2^k\mid b-a$ and $2^{k+1}\nmid b-a$; $2^{k+2}\mid b'-b$; $2^{k+1}\mid y-a$. `a :: B ++ L` parses as `(a :: B) ++ L`.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma and argument by GPT 6 Astra, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem block_reflection_absorption (a y : ℤ) (k : ℕ) (B : List ℤ)
    (hB : ∀ b ∈ B, (2 : ℤ) ^ k ∣ b - a ∧ ¬ (2 : ℤ) ^ (k + 1) ∣ b - a)
    (hG : ∀ b ∈ B, ∀ b' ∈ B, (2 : ℤ) ^ (k + 2) ∣ b' - b)
    (hy : (2 : ℤ) ^ (k + 1) ∣ y - a) (hya : y ≠ a)
    (hQ : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) (a :: B)) :
    ∃ θ' : ℕ → ℤ → Bool, Safe (treeLt θ') (a :: B ++ B.map (fun b => 2 * y - b) ++ [y]) := by sorry

end Erdos195
