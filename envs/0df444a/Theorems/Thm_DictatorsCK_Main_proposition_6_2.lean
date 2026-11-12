-- Prove2me | Theorems.Thm_DictatorsCK_Main_proposition_6_2
-- name    : DictatorsCK.Main.proposition_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:43:16.725908+00:00
-- url     : https://prove2.me/theorems/eea98d52-3d0d-4f41-8698-464601f2b02c
-- title:
--   Proposition 6.2 — simultaneous arcsine refinement: $D(g)\ge\mathrm{Dir}(\arcsin g)$ plus per-coordinate $R$-remainders, and the profile budget at a positive gap
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be nonconstant, $0<\rho<1$, $g=T_\rho f$ and $h=\arcsin g$. Write $D(g)=\sum_i\mathbb E[(L_ig)\operatorname{atanh}g]$ for the entropy production, $\mathrm{Dir}$ for the Dirichlet energy, $E_\rho(f)=\mathbb E H(g)$, and $R$, $F^{-1}$, $\ell_u$ as in (6.4), (4.1), (6.5). For every $K\subseteq[n]$,
--   $$D(g)\ge\mathrm{Dir}(h)+\rho\sum_{i\in K,\ |\hat f(i)|>0}|\hat f(i)|\,R\Big(F^{-1}\Big(\frac{E_\rho(f)}{\rho|\hat f(i)|}\Big)\Big).$$
--   Put $u=\operatorname{atanh}\rho$ and $\ell_i=\ell_u(|\hat f(i)|)$. If $G_f(\rho)=A_\rho(f)-\Phi(\rho)>0$, then
--   $$D(g)\ge\mathrm{Dir}(h)+\rho\sum_{i\in K}|\hat f(i)|\,R(\ell_i),\qquad \sum_i|\hat f(i)|\,\ell_i\le\frac{D(g)}{\rho}.$$
--
--   The first display quantifies how much entropy production exceeds the arcsine energy, coordinate by coordinate; the positive-gap part is the form used in the high-correlation argument.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: coordinates i ∈ [n] = {1, …, n} → i : Fin n = {0, …, n − 1}; reason: index shift only
--   - encoding: A_ρ(f) = I(f(X); Y_ρ) in nats → info ρ f = log 2 · mutualInformation ((1 − ρ)/2) f, the mutual information of the published goal (bits, crossover ε = (1 − ρ)/2) converted to nats; reason: the same quantity: flipping each bit with probability (1 − ρ)/2 is the published channel with ε = (1 − ρ)/2, and bits times log 2 are nats
--   - encoding: F⁻¹ : (0, ∞) → (0, ∞), the inverse of the bijection F → Finv y = a chosen v > 0 with F(v) = y (0 when there is none); reason: F is a strictly decreasing bijection of (0, ∞) (Lemma 4.1), so the chosen v is the inverse; the default is never used, since every argument of F⁻¹ here is positive
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 33 (PDF 34), Proposition 6.2

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile
import Definitions.Def_DictatorsCK_Main_Arcsine

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem proposition_6_2 {n : ℕ} (f : Cube n → Bool) (hf : IsNonconstant f) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (K : Finset (Fin n)) :
    dirichlet (fun x => Real.arcsin (noiseOperator ρ (signEncoding f) x)) +
          ρ * ∑ i ∈ K.filter (fun i => 0 < |singletonCoeff (signEncoding f) i|),
            |singletonCoeff (signEncoding f) i| *
              Rfun (Finv (condEntropy ρ f / (ρ * |singletonCoeff (signEncoding f) i|))) ≤
        dissipation (noiseOperator ρ (signEncoding f)) ∧
    (0 < gap f ρ →
      dirichlet (fun x => Real.arcsin (noiseOperator ρ (signEncoding f) x)) +
            ρ * ∑ i ∈ K, |singletonCoeff (signEncoding f) i| *
              Rfun (profileHeight (Real.artanh ρ) |singletonCoeff (signEncoding f) i|) ≤
          dissipation (noiseOperator ρ (signEncoding f)) ∧
        ∑ i, |singletonCoeff (signEncoding f) i| *
            profileHeight (Real.artanh ρ) |singletonCoeff (signEncoding f) i| ≤
          dissipation (noiseOperator ρ (signEncoding f)) / ρ) := by sorry

end DictatorsCK.Main
