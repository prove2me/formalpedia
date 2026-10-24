-- Prove2me | Theorems.Thm_Erdos195_symmetric_lifting
-- name    : Erdos195.symmetric_lifting
-- status  : Proved
-- author  : @Ethan Cheung
-- created : 2026-10-23T13:37:29.711971+00:00
-- url     : https://prove2.me/theorems/ab240984-c853-4787-b296-536ff6aaee81
-- title:
--   Symmetric lifting lemma: reflection-closed even completion absorbs an odd target
-- statement:
--   A tree witness is a function $\theta:\mathbb N\times\mathbb Z\to\{0,1\}$ on the nodes $(k,r)$ of the binary residue tree. For distinct integers $x,y$ with $k=\nu_2(y-x)$, put $x\prec_\theta y$ iff $\mathrm{bit}_k(x)=1\Leftrightarrow\theta(k,\,x\bmod 2^k)=1$. A finite word $Q$ of integers is $\theta$-safe if the sequence "the letters of $Q$ in order, then all remaining integers in $\prec_\theta$-order" contains no monotone $4$-term arithmetic progression. For a word $W$ write $W_0=(x/2 : x\in W \text{ even})$ and $W_1=((x-1)/2 : x\in W\text{ odd})$ for its normalized parity halves (order kept), and let $\theta_c(k,r)=\theta(k+1,2r+c)$ be the shifted witnesses.
--
--   **Symmetric lifting lemma.** Let $\theta$ be a tree witness with $\theta(0,0)=0$ and let $S$ be a $\theta$-safe word. (Safety with $\theta(0,0)=0$ is equivalent to $S$ being safe and *released*: every open in-order pair $(a,b)$ with $b-a$ odd ends at an even $b$.) Let $R$ be a finite list of even integers and $y\notin S$ an odd integer. Suppose
--   - the even half $(S\cdot R)_0$ is $\theta_0$-safe,
--   - the odd half $(S\cdot(y))_1$ is $\theta_1$-safe,
--   - the even entries $A$ of $S\cdot R$ satisfy $a\in A\Rightarrow 2y-a\in A$.
--
--   Then
--   $$S\cdot R\cdot(y)\ \text{ is } \theta\text{-safe}$$
--   (and hence again safe and released, with the same witness). The lemma is the positive half of the parity-decomposition analysis of root release in the tree-witness approach to Erdős Problem 195: it reduces absorbing an odd target after a released word to two half-problems plus a reflection-symmetric even completion. Companion results show the symmetric completion need not exist (e.g. from $S=(0,-2)$, $y=1$).
--
--   Formalization note: `Safe` and `treeLt` come from `Definitions.Def_Erdos195_tree`; positions are first occurrences (`List.idxOf`); halves are `filter` by `x % 2 = c` followed by `map (· / 2)` (floor division). No distinctness of the entries of $R$ is assumed.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; lemma by Sol (parity obstruction note), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem symmetric_lifting (θ : ℕ → ℤ → Bool) (h00 : θ 0 0 = false) (S R : List ℤ) (y : ℤ)
    (hS : Safe (treeLt θ) S) (hRe : ∀ r ∈ R, r % 2 = 0) (hy : y % 2 = 1) (hyS : y ∉ S)
    (hE : Safe (treeLt (fun k r => θ (k + 1) (2 * r)))
      (((S ++ R).filter (fun x => decide (x % 2 = 0))).map (· / 2)))
    (hO : Safe (treeLt (fun k r => θ (k + 1) (2 * r + 1)))
      (((S ++ [y]).filter (fun x => decide (x % 2 = 1))).map (· / 2)))
    (hsym : ∀ a ∈ S ++ R, a % 2 = 0 → 2 * y - a ∈ S ++ R) :
    Safe (treeLt θ) (S ++ R ++ [y]) := by sorry

end Erdos195
