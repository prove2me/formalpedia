-- Prove2me | Theorems.Thm_Erdos77_cgms_exponential_improvement
-- name    : Erdos77.cgms_exponential_improvement
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:31:17.318297+00:00
-- url     : https://prove2.me/theorems/5c4bc465-3266-4332-8fa4-7d6602f3a6bc
-- title:
--   Campos–Griffiths–Morris–Sahasrabudhe 2023: $R(k) \le (4-\varepsilon)^k$
-- statement:
--   There exists a constant $\varepsilon>0$ such that for all sufficiently large $k$,
--
--   $$
--   R(k)\ \le\ (4-\varepsilon)^{k}.
--   $$
--
--   This is the main theorem of Campos, Griffiths, Morris and Sahasrabudhe (2023), the first exponential improvement over the Erdős–Szekeres bound $4^{k}$. It shows $\limsup_k R(k)^{1/k}<4$.
-- source:
--   M. Campos, S. Griffiths, R. Morris, J. Sahasrabudhe, An exponential improvement for diagonal Ramsey, arXiv:2303.09521 (2023), https://arxiv.org/abs/2303.09521, Theorem 1.1.

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem cgms_exponential_improvement :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k : ℕ in atTop, (diagonalRamsey k : ℝ) ≤ (4 - ε) ^ k := by sorry
end Erdos77
