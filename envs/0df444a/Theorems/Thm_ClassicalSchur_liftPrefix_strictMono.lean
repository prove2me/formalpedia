-- Prove2me | Theorems.Thm_ClassicalSchur_liftPrefix_strictMono
-- name    : ClassicalSchur.liftPrefix_strictMono
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-09-26T21:22:27.638648+00:00
-- url     : https://prove2.me/theorems/ff384aa9-1819-43fb-b95b-e6d9a9e46472
-- title:
--   Strict monotonicity of the grid enumeration $x_L = (L \bmod m_1) + M\lfloor L/m_1 \rfloor$ for $M \ge m_1$
-- statement:
--   This lemma shows that the formula $x_L$ enumerates the grid $\{u + Mj\}$ in increasing order.
--
--   Let $m_1 \ge 1$ and $M \ge m_1$ be natural numbers, and for $L \in \mathbb{N}$ let $x_L = (L \bmod m_1) + M \lfloor L/m_1 \rfloor$, so that $x_L = u + Mj$ when $L = j m_1 + u$ with $0 \le u \le m_1 - 1$. Then the map $L \mapsto x_L$ is strictly increasing on $\mathbb{N}$:
--
--   $$
--   L < L' \implies x_L < x_{L'} \qquad \text{for all } L, L' \in \mathbb{N}.
--   $$
--
--   Consequently, for every $m_2$, the numbers $x_0 < x_1 < \dots < x_{m_1 m_2 - 1}$ are the elements of the grid $X = \{u + Mj : 0 \le u \le m_1 - 1,\ 0 \le j \le m_2 - 1\}$ in increasing order, and the lifted sequence of the Lift bundle is the jump sequence $\Delta X$, with positive entries. The prefix-sum formula for the lifted sequence, the lift lemma and the lower bound $L(n) \ge m_1 m_2$ rely on this.
--
--   **Formalization Note** The conclusion is Mathlib's `StrictMono (liftPrefix m₁ M)`, over all of $\mathbb{N}$; the note uses it only for $0 \le L \le m_1 m_2 - 1$.
-- source:
--   A. McKenna, "The Schur degree of block sums: L(4) = 16 and L(5) ≥ 49", Zenodo (2026), https://doi.org/10.5281/zenodo.22987189, §4, proof of Lemma 4.1 (because M ≥ m₁, the elements u + Mj in increasing order are x_L = u + Mj with L = j·m₁ + u). Lean source: https://github.com/mysticflounder/schur-degree-block-sums/blob/v1.0.1/lean/ClassicalSchur/Lift.lean#L37-L51 (release v1.0.1, doi:10.5281/zenodo.22987688).

import Definitions.Def_ClassicalSchurLift
import Mathlib

open ClassicalSchur

theorem ClassicalSchur.liftPrefix_strictMono {m₁ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    StrictMono (liftPrefix m₁ M) := by sorry
