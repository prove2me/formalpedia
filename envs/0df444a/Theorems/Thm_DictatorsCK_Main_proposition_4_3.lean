-- Prove2me | Theorems.Thm_DictatorsCK_Main_proposition_4_3
-- name    : DictatorsCK.Main.proposition_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:40:53.041378+00:00
-- url     : https://prove2.me/theorems/de1f8795-884e-480a-80ab-379ddecd4480
-- title:
--   Proposition 4.3 — production bound $\rho A_\rho'(f)\ge\sum_iB_{E_\rho(f)}(\rho|\hat f(i)|)$
-- statement:
--   For every nonconstant $f:\{-1,1\}^n\to\{-1,1\}$ and every $\rho\in(0,1)$,
--   $$\rho A_\rho'(f)\ge\sum_{i=1}^nB_{E_\rho(f)}\big(\rho|\hat f(i)|\big),$$
--   where $A_\rho(f)=I(f(X);Y_\rho)$ (nats), $A'_\rho(f)$ is its derivative in $\rho$ for fixed $f$, $E_\rho(f)=\mathbb E H(T_\rho f)$, and $B_e(q)=qF^{-1}(e/q)$ is the production profile.
--
--   This is the per-coordinate entropy-production inequality that, integrated from the noiseless endpoint, gives the profile clock (Theorem 4.5).
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: A_ρ(f) = I(f(X); Y_ρ) in nats → info ρ f = log 2 · mutualInformation ((1 − ρ)/2) f, the mutual information of the published goal (bits, crossover ε = (1 − ρ)/2) converted to nats; reason: the same quantity: flipping each bit with probability (1 − ρ)/2 is the published channel with ε = (1 − ρ)/2, and bits times log 2 are nats
--   - encoding: F⁻¹ : (0, ∞) → (0, ∞), the inverse of the bijection F → Finv y = a chosen v > 0 with F(v) = y (0 when there is none); reason: F is a strictly decreasing bijection of (0, ∞) (Lemma 4.1), so the chosen v is the inverse; the default is never used, since every argument of F⁻¹ here is positive
--   - encoding: A′_ρ(f), the derivative of ρ ↦ A_ρ(f) → deriv (fun r => info r f) ρ; reason: for nonconstant f, ρ ↦ A_ρ(f) is differentiable on (0, 1) (§2.4), where deriv is that derivative
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 22 (PDF 23), Proposition 4.3

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem proposition_4_3 {n : ℕ} (f : Cube n → Bool) (hf : IsNonconstant f) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) :
    ∑ i, Bprof (condEntropy ρ f) (ρ * |singletonCoeff (signEncoding f) i|) ≤
      ρ * deriv (fun r : ℝ => info r f) ρ := by sorry

end DictatorsCK.Main
