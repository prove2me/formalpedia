-- Prove2me | Theorems.Thm_Arxiv1705_08274_exp_reflection_identity
-- name    : Arxiv1705_08274.exp_reflection_identity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T02:10:02.82809+00:00
-- url     : https://prove2.me/theorems/bfc8176e-dd1b-5d74-a654-e0358751167b
-- title:
--   Eq. (21a): $e^{Ah}$ is $e^{-Ah}$ with its blocks reflected
-- statement:
--   Let $A$ be the Jacobian (5c) and $h>0$ a node width. Partition $e^{-Ah}=\begin{bmatrix}E_{11}(h)&E_{12}(h)\\E_{21}(h)&E_{22}(h)\end{bmatrix}$ into blocks of order $2N$ (eq. (7)). Then
--
--   $$e^{Ah}=\begin{bmatrix}E_{11}(-h)&E_{12}(-h)\\E_{21}(-h)&E_{22}(-h)\end{bmatrix}=\begin{bmatrix}E_{22}(h)&E_{21}(h)\\E_{12}(h)&E_{11}(h)\end{bmatrix}.$$
--
--   This relation between $e^{Ah}$ and $e^{-Ah}$ gives the second expression (23) for the response matrix.
--
--   **Formalization Note** Only the conclusion (21a) is stated. The intermediate series (19a-d) are not: as printed, their odd terms carry the signs of $e^{+Ah}$ rather than $e^{-Ah}$, and (21a) does not depend on that sign.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c002; Section I.C.2, eqs. (17), (19a-d), (20), (21a), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem exp_reflection_identity {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) :
    NormedSpace.exp (h • S.jacobian) = nodeExp S.jacobian (-h) ∧
    nodeExp S.jacobian (-h) =
      fromBlocks (nodeExp S.jacobian h).toBlocks₂₂ (nodeExp S.jacobian h).toBlocks₂₁
        (nodeExp S.jacobian h).toBlocks₁₂ (nodeExp S.jacobian h).toBlocks₁₁ := by sorry

end Arxiv1705_08274
