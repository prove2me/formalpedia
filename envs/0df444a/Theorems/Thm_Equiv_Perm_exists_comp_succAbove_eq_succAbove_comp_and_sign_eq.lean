-- Prove2me | Theorems.Thm_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
-- name    : Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/d57f67f0-c9cb-56b9-b3c4-d7232ccd7a2c
-- title:
--   Deleting a point from a permutation, with sign
-- statement:
--   For a natural number $n$, a permutation $\sigma$ of `Fin (n+1)` and an index $j \in$ `Fin (n+1)`, there exists a permutation $\tau$ of `Fin n` with two properties. First, for every $k \in$ `Fin n` one has $\sigma(\delta_j(k)) = \delta_{\sigma(j)}(\tau(k))$, where $\delta_i =$ `Fin.succAbove i` denotes the order-preserving injection `Fin n` $\to$ `Fin (n+1)` whose image omits $i$; equivalently, $\sigma \circ \delta_j = \delta_{\sigma j} \circ \tau$ as maps `Fin n` $\to$ `Fin (n+1)`. Second, the signs are related by $\operatorname{sign}(\sigma) = (-1)^{j + \sigma(j)} \operatorname{sign}(\tau)$ in the units of $\mathbb{Z}$, the exponent being the sum of the natural-number values of $j$ and of $\sigma(j)$. Thus $\tau$ is the permutation obtained from $\sigma$ by deleting the point $j$ from the source and $\sigma(j)$ from the target. Only existence is asserted; uniqueness of $\tau$ (which follows from injectivity of $\delta_{\sigma j}$) is not part of the statement.
--
--   This is the combinatorial sign bookkeeping underlying the compatibility of alternating Čech-type differentials with reindexing: a permutation of the indices of a simplex induces a permutation of each face, and the signature changes by $(-1)^{j+\sigma(j)}$. It is used in the treatment of ordered affine covers and of alternating differentials on presheaves of modules, namely by [`AlgebraicGeometry.OModulePresheaf.d_unitPullback`](thm.html#AlgebraicGeometry.OModulePresheaf.d_unitPullback), [`AlgebraicGeometry.OModulePresheaf.od_oext`](thm.html#AlgebraicGeometry.OModulePresheaf.od_oext) and [`AlgebraicGeometry.Scheme.OrderedAffineCover.obd_oesort`](thm.html#AlgebraicGeometry.Scheme.OrderedAffineCover.obd_oesort).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Equiv_Perm_exists_comp_succAbove_eq_succAbove_comp_and_sign_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Equiv.Perm.exists_comp_succAbove_eq_succAbove_comp_and_sign_eq
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (j : Fin (n + 1)) :
    ∃ τ : Equiv.Perm (Fin n), (∀ k : Fin n, σ (j.succAbove k) = (σ j).succAbove (τ k)) ∧
      Equiv.Perm.sign σ = (-1) ^ ((j : ℕ) + ((σ j) : ℕ)) * Equiv.Perm.sign τ := by sorry
