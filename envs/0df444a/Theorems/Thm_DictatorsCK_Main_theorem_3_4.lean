-- Prove2me | Theorems.Thm_DictatorsCK_Main_theorem_3_4
-- name    : DictatorsCK.Main.theorem_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:38:23.130986+00:00
-- url     : https://prove2.me/theorems/98964b21-8942-45fb-81ef-7cd734033af2
-- title:
--   Theorem 3.4 — local entropy comparison: a lower bound on $E_\rho(f)$ from one singleton coefficient, the deficit bound $M_\rho(|\hat f(i)|)$, and concavity of $M_\rho$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ have mean $\mu$, let $i\in[n]$ and $\rho\in[0,1]$. Write $E_\rho(f)=\mathbb E H(T_\rho f)$, $A_\rho(f)=I(f(X);Y_\rho)$, $\Phi=\log2-H$ and $M_\rho(a)=(1-\rho^2)H(\rho a)-(1-\rho^2a)H(\rho)$. Then
--
--   1. $$E_\rho(f)\ge\frac{1-\rho^2}{2}\Big[H\big(\mu+\rho\hat f(i)\big)+H\big(\mu-\rho\hat f(i)\big)\Big]+\rho^2|\hat f(i)|\,H(\rho);$$
--   2. $\Phi(\rho)-A_\rho(f)\ge M_\rho(|\hat f(i)|)$;
--   3. $M_\rho$ is concave on $[0,1]$, strictly concave when $0<\rho<1$, and $M_\rho(1)=0$;
--   4. consequently, if $M_\rho(A)\ge0$ for some $A\in[0,1]$ and $\max_{j\in[n]}|\hat f(j)|\ge A$, then $A_\rho(f)\le\Phi(\rho)$.
--
--   This is the local criterion: one large singleton coefficient already forces the Courtade–Kumar inequality at $\rho$, uniformly in the mean.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: coordinates i ∈ [n] = {1, …, n} → i : Fin n = {0, …, n − 1}; reason: index shift only
--   - encoding: A_ρ(f) = I(f(X); Y_ρ) in nats → info ρ f = log 2 · mutualInformation ((1 − ρ)/2) f, the mutual information of the published goal (bits, crossover ε = (1 − ρ)/2) converted to nats; reason: the same quantity: flipping each bit with probability (1 − ρ)/2 is the published channel with ε = (1 − ρ)/2, and bits times log 2 are nats
--   - encoding: max_{i∈[n]} |f̂(i)| → maxSingleton f = ⨆ i : Fin n, |f̂(i)|; reason: n ≥ 1, and the real supremum of finitely many values is their maximum
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 13 (PDF 14), Theorem 3.4

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem theorem_3_4 {n : ℕ} (f : Cube n → Bool) (i : Fin n) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (1 - ρ ^ 2) / 2 * (entropy (mean f + ρ * singletonCoeff (signEncoding f) i) +
          entropy (mean f - ρ * singletonCoeff (signEncoding f) i)) +
        ρ ^ 2 * |singletonCoeff (signEncoding f) i| * entropy ρ ≤ condEntropy ρ f ∧
    Mfun ρ |singletonCoeff (signEncoding f) i| ≤ Phi ρ - info ρ f ∧
    ConcaveOn ℝ (Set.Icc 0 1) (Mfun ρ) ∧
    (0 < ρ → ρ < 1 → StrictConcaveOn ℝ (Set.Icc 0 1) (Mfun ρ)) ∧
    Mfun ρ 1 = 0 ∧
    (∀ A : ℝ, 0 ≤ A → A ≤ 1 → 0 ≤ Mfun ρ A → A ≤ maxSingleton f → info ρ f ≤ Phi ρ) := by sorry

end DictatorsCK.Main
