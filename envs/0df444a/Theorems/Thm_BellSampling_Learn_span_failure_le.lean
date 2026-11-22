-- Prove2me | Theorems.Thm_BellSampling_Learn_span_failure_le
-- name    : BellSampling.Learn.span_failure_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T23:01:10.857325+00:00
-- url     : https://prove2.me/theorems/5cd23170-70e3-4f37-be58-f288606e32fb
-- title:
--   Learning stabilizer states, p. 2 — 2n uniform samples of an n-dimensional F₂-space fail to span it with probability ≤ 2⁻ⁿ
-- statement:
--   Let $V$ be a finite vector space over $\mathbb F_2$ of dimension $n$. Among all $|V|^{2n}$ tuples $(v_1,\dots,v_{2n})\in V^{2n}$, the number whose span is not all of $V$ is at most $2^{-n}|V|^{2n}$:
--   $$\#\{(v_1,\dots,v_{2n})\in V^{2n}:\ \operatorname{span}(v_1,\dots,v_{2n})\neq V\}\ \le\ 2^{-n}\,|V|^{2n}.$$
--   Equivalently, $2n$ independent uniform samples from $V$ fail to span it with probability at most $2^{-n}$.
--
--   This is the union bound that ends the failure analysis of Algorithm 1, applied to $V=T(\psi)$.
--
--   **Formalization Note** Stated for an abstract $n$-dimensional $\mathbb F_2$-space $V$ rather than for the subspace $T$ of $\mathbb F_2^{2n}$; the goal theorem applies it to $T$.
-- source:
--   Montanaro, Learning stabilizer states by Bell sampling, arXiv:1707.04012v2, p. 2, failure analysis after Algorithm 1, "by a union bound over all subspaces of dimension n − 1, the algorithm fails with probability at most 2^{−n}"

import Mathlib
import Definitions.Def_StabilizerRank
import Definitions.Def_BellSampling_Learn_Setting
open StabilizerRank

namespace BellSampling.Learn
theorem span_failure_le {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (n : ℕ) (hV : Module.finrank (ZMod 2) V = n) :
    (Set.ncard {v : Fin (2 * n) → V | Submodule.span (ZMod 2) (Set.range v) ≠ ⊤} : ℝ) ≤
      1 / 2 ^ n * (Fintype.card V : ℝ) ^ (2 * n) := by sorry
end BellSampling.Learn
