-- Prove2me | Theorems.Thm_Arxiv1705_08274_single_node_response_symmetric
-- name    : Arxiv1705_08274.single_node_response_symmetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T02:11:59.658831+00:00
-- url     : https://prove2.me/theorems/1e7ca061-2418-5400-86a7-feb88a6d1a12
-- title:
--   Eqs. (13), (14), (24): the single node response matrix is symmetric
-- statement:
--   Let $A$ be the Jacobian (5c), $h>0$ a node width, and partition $e^{-Ah}=[[E_{11},E_{12}],[E_{21},E_{22}]]$. Assume $E_{22}$ is invertible (the paper's "suitable invertibility"). Let
--
--   $$R=\begin{bmatrix}E_{12}&-I\\E_{22}&0\end{bmatrix}^{-1}\begin{bmatrix}0&-E_{11}\\I&-E_{21}\end{bmatrix}$$
--
--   be the response matrix (11b) of the node, which maps $[I^-_{j+1};I^+_j]$ to $[I^-_j;I^+_{j+1}]$. Then
--
--   $$R=\begin{bmatrix}E_{22}^{-1}&-E_{22}^{-1}E_{21}\\E_{12}E_{22}^{-1}&E_{11}-E_{12}E_{22}^{-1}E_{21}\end{bmatrix},$$
--
--   and $R$ is symmetric: $R=\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$ with
--
--   $$T_n=E_{22}^{-1}=E_{11}-E_{12}E_{22}^{-1}E_{21},\qquad R_f=-E_{22}^{-1}E_{21}=E_{12}E_{22}^{-1}.$$
--
--   This is the mathematical form of collision symmetry: the transmittance and reflectance of a homogeneous node are the same from either face. All the doubling and adding formulas of the paper rest on it.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c003; Section I.C.1-2, eqs. (11a,b), (13), (14), (16b), (22b), (23), (24), PDF pp. 7-11

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem single_node_response_symmetric {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) (hE : IsUnit (nodeExp S.jacobian h).toBlocks₂₂.det) :
    let E := nodeExp S.jacobian h
    let R := respOfProp E
    R = fromBlocks E.toBlocks₂₂⁻¹ (-(E.toBlocks₂₂⁻¹ * E.toBlocks₂₁)) (E.toBlocks₁₂ * E.toBlocks₂₂⁻¹)
      (E.toBlocks₁₁ - E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ * E.toBlocks₂₁) ∧
    IsSymmetricResponse R ∧
    E.toBlocks₂₂⁻¹ = E.toBlocks₁₁ - E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ * E.toBlocks₂₁ ∧
    -(E.toBlocks₂₂⁻¹ * E.toBlocks₂₁) = E.toBlocks₁₂ * E.toBlocks₂₂⁻¹ := by sorry

end Arxiv1705_08274
