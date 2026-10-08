-- Prove2me | Theorems.Thm_AlgebraicPCSP_Colouring_lemma_6_4
-- name    : AlgebraicPCSP.Colouring.lemma_6_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:29.857168+00:00
-- url     : https://prove2.me/theorems/06777ba0-2c96-41dd-b15a-3315a00fa862
-- title:
--   Lemma 6.4 — Pol(K_k, K_{2k−1}) does not contain an Olšák function (k ≥ 3)
-- statement:
--   Let $k \ge 3$, and let $\mathbf K_k = (E_k; \neq_k)$ be the complete graph on $E_k = \{0, \dots, k-1\}$. No polymorphism from $\mathbf K_k$ to $\mathbf K_{2k-1}$ is an Olšák function: there is no 6-ary $o \in \mathrm{Pol}(\mathbf K_k, \mathbf K_{2k-1})$, that is, no $(2k-1)$-colouring $o$ of the sixth power $\mathbf K_k^6$, with
--   $$
--   o(x, x, y, y, y, x) = o(x, y, x, y, x, y) = o(y, x, x, x, y, y) \quad \text{for all } x, y \in E_k .
--   $$
--
--   Together with Theorem 6.2 this is the combinatorial heart of the NP-hardness of distinguishing $k$-colourable graphs from graphs that are not even $(2k-1)$-colourable. It is sharp: by Proposition 10.1, $\mathrm{Pol}(\mathbf K_k, \mathbf K_{2k})$ does contain an Olšák function.
--
--   **Formalization Note** The hypothesis $k \ge 3$ is the standing assumption of §6.2 (p. 38: "for all $k \ge 3$"); with it, $2k - 1$ is computed in $\mathbb N$ without truncation and $k \le 2k-1$, so $(\mathbf K_k, \mathbf K_{2k-1})$ is a PCSP template.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, p. 38, Lemma 6.4 (standing assumption k ≥ 3 from §6.2, p. 38)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting
import Definitions.Def_AlgebraicPCSP_Colouring_Minion
import Definitions.Def_AlgebraicPCSP_Colouring_Structures

namespace AlgebraicPCSP.Colouring

open PCSPBLPAff.Symmetric

/-- Lemma 6.4 (arXiv:1811.00970v3, p. 38): for every `k ≥ 3`, `Pol(K_k, K_{2k−1})` does not
contain an Olšák function. The bound `k ≥ 3` is the standing assumption of §6.2 (p. 38); with
it, `2 * k - 1` involves no truncated subtraction. -/
theorem lemma_6_4 (k : ℕ) (hk : 3 ≤ k) :
    ¬ ContainsOlsak
      (Pol (Kgraph k) (Kgraph (2 * k - 1)) (Kgraph_template (by omega))) := by sorry

end AlgebraicPCSP.Colouring
