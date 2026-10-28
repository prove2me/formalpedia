-- Prove2me | Theorems.Thm_DecisionForest_Universal_fullTree_spec
-- name    : DecisionForest.Universal.fullTree_spec
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-23T08:38:42.859624+00:00
-- url     : https://prove2.me/theorems/f775162c-bc6d-4881-b953-48ab8f69ba15
-- title:
--   Proof of Theorem 1, pp. ec1–ec2 — the balanced tree (EC.1)–(EC.4) has 2^N leaves, one per assortment, depth N + 1, and satisfies Requirement 3
-- statement:
--   Let $N\ge 0$ and let $\mathbf o=(o_S)_{S\subseteq\mathcal N}$ assign a purchase option $o_S\in\mathcal N^+$ to every assortment. Let $t_{\mathbf o}$ be the balanced tree of the proof of Theorem 1: every split at distance $k-1$ from the root checks product $k$ ($k=1,\dots,N$, equations (EC.1)–(EC.4)), and the leaf reached by assortment $S$ carries the option $o_S$. Then:
--
--   1. for every assortment $S\subseteq\mathcal N$, a customer following $t_{\mathbf o}$ and offered $S$ purchases $o_S$:
--   $$\hat A(S,t_{\mathbf o})=o_S ;$$
--   2. $t_{\mathbf o}$ has exactly $2^N$ leaves;
--   3. $\mathrm{Depth}(t_{\mathbf o})=N+1$;
--   4. $t_{\mathbf o}$ satisfies Requirement 3.
--
--   Item 1 is the one-to-one correspondence between the leaves of the tree and the $2^N$ assortments; items 3 and 4 place $t_{\mathbf o}$ in $F_{N+1}$ as soon as it also satisfies Requirement 2.
--
--   **Formalization Note** The tuple $\mathbf o$ is a function `o : Finset (Fin N) → Option (Fin N)` and $t_{\mathbf o}$ is `fullTree o`, which splits on the products `0, …, N-1` (the paper's $1,\dots,N$) level by level.
--
--   Differences from the source:
--   - encoding: leaves $l_1,\dots,l_{2^N}$ enumerated left to right and matched with assortments $S_1,\dots,S_{2^N}$ → leaves indexed directly by assortments, the correspondence stated as $\hat A(S,t_{\mathbf o})=o_S$; reason: same tree and same correspondence, no enumeration needed.
--   - encoding: products $\{1,\dots,N\}$ → `Fin N` (product $k$ is `k - 1`); reason: Lean convention, same instances.
--   - reading: the proof uses that each constructed tree satisfies Requirement 3 (so that the trees kept lie in $F_{N+1}$) without stating it → stated as clause 4; reason: it is what "a distribution over $F_{N+1}$" in Theorem 1 requires of the constructed trees.
-- source:
--   Chen and Mišić, Decision Forest: A Nonparametric Approach to Modeling Irrational Choice, arXiv:1904.11532v3, pp. ec1–ec2 (PDF 30–31), proof of Theorem 1, (EC.1)–(EC.4) and the paragraph after Figure EC.2

import Mathlib
import Definitions.Def_DecisionForest_Universal_Setting

namespace DecisionForest.Universal

theorem fullTree_spec (N : ℕ) (o : Finset (Fin N) → Option (Fin N)) :
    (∀ S : Finset (Fin N), choose (fullTree o) S = o S) ∧ numLeaves (fullTree o) = 2 ^ N ∧
      depth (fullTree o) = N + 1 ∧ Req3 (fullTree o) := by sorry

end DecisionForest.Universal
