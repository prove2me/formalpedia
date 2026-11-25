-- Prove2me | Theorems.Thm_Arxiv1705_08274_rk5_symmetric
-- name    : Arxiv1705_08274.rk5_symmetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:32:25.007111+00:00
-- url     : https://prove2.me/theorems/b911d5ae-528e-4625-977b-364854a74e26
-- title:
--   Eqs. (50a)-(54): the RK5 response matrix is symmetric
-- statement:
--   Let $A$ be the Jacobian (5c) and $h>0$. Write $e^{-Ah}=[e^{Ah/2}]^{-1}e^{-Ah/2}$ and estimate $P^*(h)\simeq e^{Ah/2}$ by one step of Fehlberg's fifth-order Runge-Kutta method for $\frac{d\xi}{d\tau}=\frac A2\xi$:
--
--   $$P^*(h)=I+\sum_{i=1}^6b_ig_i(h),\qquad g_i(h)=\frac h2A\Big[I+\sum_{n=1}^{i-1}a_{in}g_n(h)\Big],$$
--
--   with the coefficients of Table 1, and set $P(h)=P^*(-h)$ (50b), (52a). Then:
--
--   1. there are constants $e_1,\dots,e_6$, the same for every model and node width, with $P^*(h)=I+\sum_{k=1}^6e_kh^kA^k$ (53b);
--   2. $P=\begin{bmatrix}P^*_{22}&P^*_{21}\\P^*_{12}&P^*_{11}\end{bmatrix}$, and the response matrix has the form (54), $R=\begin{bmatrix}-P^*_{21}&P^*_{11}\\-P^*_{11}&P^*_{21}\end{bmatrix}^{-1}\begin{bmatrix}-P^*_{12}&P^*_{22}\\-P^*_{22}&P^*_{12}\end{bmatrix}$;
--   3. if $P^*_{11}\mp P^*_{21}$ are invertible, $R$ is symmetric.
--
--   **Formalization Note** The approximation $P^*(h)\simeq e^{Ah/2}$ and the efficiency claim are not stated. The Butcher coefficients are those of Table 1 (Fehlberg's fifth-order weights $b=(16/135,0,6656/12825,28561/56430,-9/50,2/55)$).
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c011; Section II.A.3, eqs. (50a,b), (51a-d), (52a,b), (53a,b), (54), Table 1, PDF pp. 23-25

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem rk5_symmetric {N : ℕ} (S : DOModel N) (hS : S.Admissible) (h : ℝ) (hh : 0 < h) :
    (∃ e : ℕ → ℝ, ∀ (N' : ℕ) (S' : DOModel N'), S'.Admissible → ∀ t : ℝ,
      rk5Pstar S'.jacobian t = 1 + ∑ k ∈ Finset.Icc 1 6, (e k * t ^ k) • S'.jacobian ^ k) ∧
    let Ps := rk5Pstar S.jacobian h
    let P := rk5Pstar S.jacobian (-h)
    P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ ∧
    respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ ∧
    (IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det → IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det →
      IsSymmetricResponse (respOfPair Ps P)) := by sorry

end Arxiv1705_08274
