-- Prove2me | Theorems.Thm_DictatorsCK_Main_lemma_2_1
-- name    : DictatorsCK.Main.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:12.66178+00:00
-- url     : https://prove2.me/theorems/e38444ec-56a6-4f8c-b35a-b1ec5450c8dd
-- title:
--   Lemma 2.1 — coordinate compression: an increasing $g$ with the same mean, $A_\rho(g)\ge A_\rho(f)$ for every $\rho$, and $\hat g(i)\ge|\hat f(i)|$
-- statement:
--   Let $n\ge1$ and let $f:\{-1,1\}^n\to\{-1,1\}$ be Boolean. Write $A_\rho(f)=I(f(X);Y_\rho)$ (nats) for the information about $f(X)$ kept by the $\rho$-noisy copy $Y_\rho$ of the uniform input $X$, $\hat f(i)=\mathbb E[f(X)X_i]$ for the singleton Fourier coefficients and $\delta(f)=\min_{i,\sigma}\mathbb P(f(X)\ne\sigma X_i)$ for the distance to the nearest signed dictator. Then there is an **increasing** Boolean $g$ (that is, $g(x)\le g(y)$ whenever $x_i\le y_i$ for all $i$), chosen independently of $\rho$, with
--   $$\mathbb E g=\mathbb E f,\qquad A_\rho(g)\ge A_\rho(f)\ \ \text{for every }\rho\in[0,1],\qquad \hat g(i)\ge|\hat f(i)|\ \ \text{for every }i\in[n],$$
--   and in particular $\delta(g)\le\delta(f)$.
--
--   This is the reduction of the Courtade–Kumar problem to increasing functions: one fixed monotone function dominates $f$ at every noise level, and its singleton coefficients are influences.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: coordinates i ∈ [n] = {1, …, n} → i : Fin n = {0, …, n − 1}; reason: index shift only
--   - encoding: A_ρ(f) = I(f(X); Y_ρ) in nats → info ρ f = log 2 · mutualInformation ((1 − ρ)/2) f, the mutual information of the published goal (bits, crossover ε = (1 − ρ)/2) converted to nats; reason: the same quantity: flipping each bit with probability (1 − ρ)/2 is the published channel with ε = (1 − ρ)/2, and bits times log 2 are nats
--   - encoding: increasing: f(x) ≤ f(y) whenever x_i ≤ y_i for all i → IsIncreasing (signEncoding f), with the Bool order false < true; reason: false ↦ −1 < true ↦ 1, so the coordinate orders agree
--   - encoding: δ(f) = min over i ∈ [n], σ ∈ {−1, 1} of P(f(X) ≠ σX_i) → dictatorDistance f = ⨅ over (i, σ) ∈ Fin n × Bool of the uniform average of the indicator of f(x) ≠ σ x_i (σ = 1 ⇔ true); reason: the infimum of finitely many reals is their minimum, and the uniform average of an indicator is its probability
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 9 (PDF 10), Lemma 2.1

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem lemma_2_1 {n : ℕ} (hn : 1 ≤ n) (f : Cube n → Bool) :
    ∃ g : Cube n → Bool,
      IsIncreasing (signEncoding g) ∧
      mean g = mean f ∧
      (∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → info ρ f ≤ info ρ g) ∧
      (∀ i : Fin n, |singletonCoeff (signEncoding f) i| ≤ singletonCoeff (signEncoding g) i) ∧
      dictatorDistance g ≤ dictatorDistance f := by sorry

end DictatorsCK.Main
