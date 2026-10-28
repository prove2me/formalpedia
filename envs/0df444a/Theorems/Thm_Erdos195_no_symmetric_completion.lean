-- Prove2me | Theorems.Thm_Erdos195_no_symmetric_completion
-- name    : Erdos195.no_symmetric_completion
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T13:11:36.507948+00:00
-- url     : https://prove2.me/theorems/907a2e8d-696a-41c4-99bd-2594d06f9810
-- title:
--   No node-consistent extension of $(0,-1)$ is symmetric about $1/2$
-- statement:
--   For a finite word $A$ of integers, an in-order pair $(x,y)$ of $A$ ($x$ occurs before $y$) is open if $2y-x\notin A$ and $3y-2x\notin A$. It lies at the node $(k,\,x\bmod 2^k)$ of the binary residue tree, where $k=\nu_2(y-x)$, and it forces the bit $\mathrm{bit}_k(y)=\lfloor y/2^k\rfloor\bmod 2$ there. The word satisfies SAFE(ii), or node consistency, if no node is forced to both bits by open pairs: any two open pairs at the same node force the same bit. There is no finite word
--   $$A=(0,-1,\dots)$$
--   satisfying SAFE(ii) whose support is invariant under $u\mapsto 1-u$. Invariance would force $2\in A$ and $\min A+\max A=1$, so the extremes would have opposite parity, contradicting the extremal-parity lemma. In the tree-witness approach to Erdős Problem 195 this excludes the natural symmetric (reflection) completion of the even half that arises when releasing the root.
--
--   Formalization note: SAFE(ii) is stated inline exactly as the second conjunct of `Erdos195.exists_treeLt_safe_iff`. Positions are `List.idxOf`, $\nu_2$ is `padicValInt 2`, and $\mathrm{bit}_k$ is `bitOne` from `Definitions.Def_Erdos195_defs`. Only the closure $u\in A\Rightarrow 1-u\in A$ is assumed. Every tree-safe word satisfies SAFE(ii).
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); tree-witness framework; parity obstruction by Sol, Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos195_tree

namespace Erdos195

theorem no_symmetric_completion (A rest : List ℤ) (hA : A = 0 :: -1 :: rest)
    (hii : ∀ x y x' y' : ℤ, x ∈ A → y ∈ A → A.idxOf x < A.idxOf y →
      2 * y - x ∉ A → 3 * y - 2 * x ∉ A →
      x' ∈ A → y' ∈ A → A.idxOf x' < A.idxOf y' →
      2 * y' - x' ∉ A → 3 * y' - 2 * x' ∉ A →
      padicValInt 2 (y - x) = padicValInt 2 (y' - x') →
      x % 2 ^ padicValInt 2 (y - x) = x' % 2 ^ padicValInt 2 (y - x) →
      (bitOne y (padicValInt 2 (y - x)) ↔ bitOne y' (padicValInt 2 (y - x))))
    (hsym : ∀ u ∈ A, 1 - u ∈ A) : False := by sorry

end Erdos195
