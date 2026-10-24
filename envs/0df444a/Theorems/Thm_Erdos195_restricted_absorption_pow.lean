-- Prove2me | Theorems.Thm_Erdos195_restricted_absorption_pow
-- name    : Erdos195.restricted_absorption_pow
-- status  : Open
-- author  : @Ethan Cheung
-- created : 2026-10-23T15:50:42.624361+00:00
-- url     : https://prove2.me/theorems/06c8937c-48d1-47d6-8617-9c2f23b83dff
-- title:
--   Restricted absorption at every 2-adic depth L ≥ 5: explicit 2n+4 batch for (a)·A·(b)
-- statement:
--   A tree witness is a function $\theta(k,r)\in\{0,1\}$ on the nodes $(k,r)$, $0\le r<2^k$, of the binary tree of residues. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=\theta(k,\,x\bmod 2^k)$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. $Q$ is SAFE if it is $\theta$-safe for some tree witness $\theta$. For a word $A=(x_1,\dots,x_n)$ and an affine map $g$, $g(A)=(g(x_1),\dots,g(x_n))$ keeps the original order, and $\cdot$ denotes concatenation.
--
--   **Theorem (restricted absorption at every depth $L\ge5$).** Let $L\ge 5$, let $r$ be odd, and let $A$ be a SAFE word all of whose letters are $\equiv r\pmod{2^L}$. Let $a$ be even, $b\equiv r+2\pmod 4$, and let $y\neq a$ satisfy
--   $$2y-b\equiv r+2^{L-1}\pmod{2^L}.$$
--   Then the word
--   $$a\cdot A\cdot b\cdot(2y-b)\cdot(2y-A)\cdot y\cdot(12y-11b)\cdot(10y-10b+A)\cdot(6y-5b)$$
--   is SAFE.
--
--   Equivalently, put $c=2y-b$. If all letters of $A$ lie in the sibling ball of $c$ at some common $2$-adic depth $\nu=L-1\ge4$, then the prefix $(a)\cdot A\cdot(b)$ absorbs the target $y$ with the explicit batch of $2|A|+4$ letters above. There is no size condition on $y$. For a fixed prefix whose block $A$ is $\equiv r\pmod{2^{L_0}}$, this covers every target with $4\le\nu_2(2y-b-r)\le L_0-1$. The case $L=5$ is Erdos195.restricted_absorption (GPT Astra's mod-32 corollary). This is the general-$L$ form of Astra's corollary. It is a positive absorption result for one infinite class of words in the tree-witness approach to Erdős Problem 195. It does not settle the problem.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; general-L form of GPT Astra's restricted absorption corollary, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem restricted_absorption_pow (L : ℕ) (hL : 5 ≤ L) (a b y r : ℤ) (A : List ℤ) (hr : r % 2 = 1)
    (hAL : ∀ x ∈ A, x % 2 ^ L = r % 2 ^ L) (ha : a % 2 = 0) (hb : b % 4 = (r + 2) % 4)
    (hcL : (2 * y - b) % 2 ^ L = (r + 2 ^ (L - 1)) % 2 ^ L) (hya : y ≠ a)
    (hS : ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ) A) :
    ∃ θ : ℕ → ℤ → Bool, Safe (treeLt θ)
      (a :: A ++ [b, 2 * y - b] ++ A.map (fun x => 2 * y - x) ++ [y, 12 * y - 11 * b] ++
        A.map (fun x => 10 * y - 10 * b + x) ++ [6 * y - 5 * b]) := by sorry

end Erdos195
