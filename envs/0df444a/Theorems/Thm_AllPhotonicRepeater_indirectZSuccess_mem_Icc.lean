-- Prove2me | Theorems.Thm_AllPhotonicRepeater_indirectZSuccess_mem_Icc
-- name    : AllPhotonicRepeater.indirectZSuccess_mem_Icc
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:22:00.898177+00:00
-- url     : https://prove2.me/theorems/7ce9f8ed-27d3-4695-88a6-5bd7df8300dc
-- title:
--   Eqs. (A3), (A12): $R_k$, $P_Z$, $P_X$ lie in $[0,1]$
-- statement:
--   Let $0\le\epsilon_0\le1$, let $l\in\mathbb N$ and let $b_0,\dots,b_l$ be branching parameters. Then for every level $k$ the indirect $Z$-measurement success probability (A3) is a probability,
--   $$
--   0\le R_k\le 1,
--   $$
--   and consequently $0\le P_Z\le1$ for the loss-tolerant $Z$ measurement (A13) and $0\le P_X\le1$ for the loss-tolerant $X$ measurement (A16).
--
--   The paper reads $R_k$ as a success probability, which (A12) writes as the binomial sum $\sum_{m_k=1}^{b_k}T_k(m_k)$. This item makes that reading a statement about the recursion, and is used whenever a factor of (C1) is bounded.
--
--   Differences from the source:
--   - reading: (A3) printed for $1\le k\le l$ → $R_k$ given by (A3) also at $k=0$; reason: (A16) reads $P_X=R_0$, and (A7), (A9), (A12) give $R_k=1-(1-S_k)^{b_k}$ at every level, $k=0$ included
--   - encoding: $R_{l+1}:=0$ and $b_{l+1}:=0$ → $R_k=0$ and $b_k$ read as $0$ for every $k>l$; reason: $R_{l+2}$ enters only $R_l$, raised to the power $b_{l+1}=0$, so its value never matters; same instances
--   - generalization: $\epsilon_0<0.5$ (standing assumption, p. 11) → $0\le\epsilon_0\le1$; reason: the bound holds for every loss probability; it specializes to the paper's range
--   - reading: $R_k$ called a success probability; (A12) $R_k=\sum_{m_k=1}^{b_k}T_k(m_k)$ → $0\le R_k\le1$ for every $k$, and $P_Z,P_X\in[0,1]$; reason: the paper asserts no inequality; this is the exact content of reading $R_k$, $P_Z$, $P_X$ as probabilities
-- source:
--   Azuma, Tamaki, Lo, All photonic quantum repeaters, arXiv:1309.7207v1, App. A1, Eq. (A3), p. 7; App. A2, Eq. (A12), p. 8; Eqs. (A13), (A16), p. 9

import Mathlib
import Definitions.Def_AllPhotonicRepeater_zSuccess
import Definitions.Def_AllPhotonicRepeater_xSuccess

set_option autoImplicit false

namespace AllPhotonicRepeater

/-- Azuma, Tamaki, Lo, *All photonic quantum repeaters*, arXiv:1309.7207v1, App. A1, Eq. (A3),
p. 7, and App. A2, Eq. (A12), p. 8: for a per-photon loss probability `0 ≤ ε0 ≤ 1`, the
indirect `Z`-measurement success `R_k` of every level `k` of every tree is a probability,
`0 ≤ R_k ≤ 1`; consequently `0 ≤ P_Z ≤ 1` (A13) and `0 ≤ P_X ≤ 1` (A16), p. 9.

**Formalization Note** `R_k` is (A3) at every `k ≤ l`, `k = 0` included, and `0` for `k > l`
(see `indirectZSuccess`). -/
theorem indirectZSuccess_mem_Icc (ε0 : ℝ) (h0 : 0 ≤ ε0) (h1 : ε0 ≤ 1) (l : ℕ) (b : ℕ → ℕ) :
    (∀ k : ℕ, 0 ≤ indirectZSuccess ε0 l b k ∧ indirectZSuccess ε0 l b k ≤ 1) ∧
    (0 ≤ zSuccess ε0 l b ∧ zSuccess ε0 l b ≤ 1) ∧
    (0 ≤ xSuccess ε0 l b ∧ xSuccess ε0 l b ≤ 1) := by sorry

end AllPhotonicRepeater
