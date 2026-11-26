-- Prove2me | Theorems.Thm_Arxiv1705_08274_doubling_exiting_intensities
-- name    : Arxiv1705_08274.doubling_exiting_intensities
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T02:17:55.02816+00:00
-- url     : https://prove2.me/theorems/c6e4d400-a1c1-459d-a3a2-b7af7a65a5e5
-- title:
--   Eqs. (34a)-(34c): exiting intensities of a doubled slab on a Lambertian reflector
-- statement:
--   Let a node have symmetric response $R=\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$ (blocks of order $2N$), and let $Q_n$ be the response after $n\ge1$ doublings. These combine two copies of the current response with eqs. (28), and every step is assumed admissible. Then $Q_n=\begin{bmatrix}Q_{n11}&Q_{n12}\\Q_{n12}&Q_{n11}\end{bmatrix}$ is symmetric. Let $\lambda_0\ge0$ be the Lambertian reflection coefficient and $D$ the $2\times2$ reflection matrix. Suppose the intensities satisfy
--
--   $$\begin{bmatrix}I^-_0\\I^+_n\end{bmatrix}=Q_n\begin{bmatrix}I^-_n\\I^+_0\end{bmatrix}\ \ (30),\qquad I^-_n=2\lambda_0\mathcal DMWI^+_n\ \ (32a),$$
--
--   and that $K=I-2\lambda_0Q_{n12}\mathcal DMW$ is invertible. Then
--
--   $$I^+_n=K^{-1}Q_{n11}I^+_0,\qquad I^-_n=2\lambda_0\mathcal DMWK^{-1}Q_{n11}I^+_0,\qquad I^-_0=\big\{Q_{n12}+2\lambda_0Q_{n11}\mathcal DMWK^{-1}Q_{n11}\big\}I^+_0.$$
--
--   These are eqs. (34a)-(34c): the transmitted and reflected intensities of the slab in terms of the incident beam.
--
--   **Formalization Note** The node response is taken in the symmetric form (14), and the paper's response $R$ of eq. (22b) is one instance. The symmetry of $Q_n$, which the paper uses when it writes (30) as (33a,b), is part of the conclusion.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c006; Section I.E.1, eqs. (30), (31), (32a,b), (33a,b), (34a)-(34c), PDF pp. 15-16

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem doubling_exiting_intensities {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (Tn Rf : Matrix (Dir N) (Dir N) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hdbl : ∀ j, j < k → CanAdd (dblSeq (fromBlocks Tn Rf Rf Tn) j) (dblSeq (fromBlocks Tn Rf Rf Tn) j))
    (lam0 : ℝ) (hlam0 : 0 ≤ lam0) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (I0m I0p Inm Inp : Dir N → ℝ)
    (h30 : Sum.elim I0m Inp = dblSeq (fromBlocks Tn Rf Rf Tn) k *ᵥ Sum.elim Inm I0p)
    (h32 : Inm = ((2 * lam0) • (reflArray D * S.muMat * S.wMat)) *ᵥ Inp)
    (hK : IsUnit (1 - (2 * lam0) • ((dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₂ *
      reflArray D * S.muMat * S.wMat)).det) :
    let Q₁₁ := (dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₁
    let Q₁₂ := (dblSeq (fromBlocks Tn Rf Rf Tn) k).toBlocks₁₂
    let K := 1 - (2 * lam0) • (Q₁₂ * reflArray D * S.muMat * S.wMat)
    IsSymmetricResponse (dblSeq (fromBlocks Tn Rf Rf Tn) k) ∧
    Inp = (K⁻¹ * Q₁₁) *ᵥ I0p ∧
    Inm = ((2 * lam0) • (reflArray D * S.muMat * S.wMat) * K⁻¹ * Q₁₁) *ᵥ I0p ∧
    I0m = (Q₁₂ + (2 * lam0) • (Q₁₁ * reflArray D * S.muMat * S.wMat * K⁻¹ * Q₁₁)) *ᵥ I0p := by sorry

end Arxiv1705_08274
