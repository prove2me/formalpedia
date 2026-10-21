-- Prove2me | Theorems.Thm_AffineStorage_Ruin_eq_10
-- name    : AffineStorage.Ruin.eq_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:36:34.639552+00:00
-- url     : https://prove2.me/theorems/dd22d6be-f5f6-4eb5-b7dd-0cfd5e17a84c
-- title:
--   Eq. (10), p. 1287 (PDF 8) — ϱ(0)I1(0) + φ(μ)I2(0) = −I3(0)
-- statement:
--   Let $\varrho(0)$ and $\varphi(\mu)$ be the model's constants, $F_\star$ any primitive of $F$ on $(0,\mu)\cup(\mu,\infty)$, and $I_k(\vartheta)=\int_\vartheta^\infty G_k(\eta)e^{-F_\star(\eta)}\,d\eta$. Then
--   $$\varrho(0)I_1(0)+\varphi(\mu)I_2(0)=-I_3(0).\tag{10}$$
--
--   This is the condition $I(0)=0$, forced by the finiteness of $\varphi$ near $0$, where $F_\star\to\infty$. With (11) it forms the linear system whose solution (12) expresses $\varrho(0)$ and $\varphi(\mu)$ in terms of the model's data.
-- source:
--   Boxma & Mandjes, Affine storage and insurance risk models, Math. Oper. Res. 46(4) (2021), p. 1287 (PDF 8), eq. (10)

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace AffineStorage.Ruin

theorem eq_10 (P : Params) (hS : P.Standing) {Ω : Type*} [MeasurableSpace Ω]
    (B : Basis Ω) (hB : B.IsValid P) (Fs : ℝ → ℝ) (hF : IsPrimitiveF P Fs) :
    rho B P 0 * I (G1 P) Fs 0 + phi B P P.μ * I (G2 P) Fs 0 = -I (G3 P) Fs 0 := by sorry

end AffineStorage.Ruin
