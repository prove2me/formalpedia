-- Prove2me | Theorems.Thm_AffineStorage_Ruin_eq_11
-- name    : AffineStorage.Ruin.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:48.015234+00:00
-- url     : https://prove2.me/theorems/0dbe0a4b-31b0-46da-8acd-3a665b0987ff
-- title:
--   Eq. (11), p. 1287 (PDF 8) — ϱ(0)I1(μ) + φ(μ)I2(μ) = −I3(μ)
-- statement:
--   Let $\varrho(0)$ and $\varphi(\mu)$ be the model's constants: the expected discounted penalty from initial level $0$, and the transform $\varphi$ at $\vartheta=\mu$. Let $F_\star$ be any primitive of $F$ on $(0,\mu)\cup(\mu,\infty)$ and $I_k(\vartheta)=\int_\vartheta^\infty G_k(\eta)e^{-F_\star(\eta)}\,d\eta$. Then
--   $$\varrho(0)I_1(\mu)+\varphi(\mu)I_2(\mu)=-I_3(\mu).\tag{11}$$
--
--   This is the condition $I(\mu)=0$, forced by the finiteness of $\varphi$ near $\mu$, where $F_\star\to\infty$. It is one of the two linear equations that determine $\varrho(0)$ and $\varphi(\mu)$.
--
--   **Formalization Note.** The identity holds for every choice of the two additive constants in $F_\star$: both sides scale by the same factor.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1287 (PDF 8), eq. (11)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem eq_11 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    rho B P 0 * I (G1 P) Fs P.μ + phi B P P.μ * I (G2 P) Fs P.μ = -I (G3 P) Fs P.μ := by sorry

end AffineStorage.Ruin
