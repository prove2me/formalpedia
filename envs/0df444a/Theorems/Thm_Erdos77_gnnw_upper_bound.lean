-- Prove2me | Theorems.Thm_Erdos77_gnnw_upper_bound
-- name    : Erdos77.gnnw_upper_bound
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T18:34:23.91036+00:00
-- url     : https://prove2.me/theorems/bb6839d2-fc28-4e58-8842-5598200cd89d
-- title:
--   Gupta–Ndiaye–Norin–Wei 2024: $R(k) \le 3.8^{k+o(k)}$
-- statement:
--   For every $\delta>0$ there is $k_0$ such that for all $k\ge k_0$,
--
--   $$
--   R(k)\ \le\ 3.8^{(1+\delta)k}.
--   $$
--
--   Equivalently, $R(k)\le 3.8^{k+o(k)}$, the main result of Gupta, Ndiaye, Norin and Wei (2024), obtained by optimising the method of Campos–Griffiths–Morris–Sahasrabudhe. It gives $\limsup_k R(k)^{1/k}\le 3.8$, the best currently known upper bound on the quantity in Erdős Problem 77.
--
--   **Formalization Note** The $o(k)$ term in the exponent is encoded as: for every $\delta>0$, eventually the exponent $(1+\delta)k$ suffices. This is equivalent to the existence of a function $f(k)=o(k)$ with $R(k)\le 3.8^{k+f(k)}$ for all large $k$.
-- source:
--   P. Gupta, N. Ndiaye, S. Norin, L. Wei, Optimizing the CGMS upper bound on Ramsey numbers, arXiv:2407.19026 (2024), https://arxiv.org/abs/2407.19026 (main result stated in the abstract: R(k) ≤ (3.8)^{k+o(k)}).

import Mathlib
import Definitions.Def_Erdos77_diagonal_ramsey
open Filter Topology

namespace Erdos77
theorem gnnw_upper_bound (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop, (diagonalRamsey k : ℝ) ≤ (3.8 : ℝ) ^ ((1 + δ) * (k : ℝ)) := by sorry
end Erdos77
