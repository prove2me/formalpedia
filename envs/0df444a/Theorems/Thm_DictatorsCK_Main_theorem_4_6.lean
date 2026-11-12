-- Prove2me | Theorems.Thm_DictatorsCK_Main_theorem_4_6
-- name    : DictatorsCK.Main.theorem_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:41:05.848297+00:00
-- url     : https://prove2.me/theorems/3081e63e-5957-4e75-9c8e-e99db4998575
-- title:
--   Theorem 4.6 — propagation of a clock bound to every larger correlation, with $E_\rho(f)\ge H(\rho)\rho^{-\epsilon}$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ satisfy $W_1(f)>0$, and let $Q$ have the finite-sum form (4.5): $Q(y)=\sum_{j=1}^Jc_jB_y(q_j)$ with $J\ge1$, $c_j>0$, $q_j\in(0,1]$ fixed, and $Q(y)\le P_f(y)$ for every $y>0$. Write $T_Q(v)=\int_0^v\frac{dy}{y+Q(y)}$. Fix $0<\rho_0<1$ and $\epsilon\in[0,1)$, and suppose
--   $$T_Q\big(H(\rho_0)/\rho_0\big)\le(1-\epsilon)\log(1/\rho_0).$$
--   Then for every $\rho\in[\rho_0,1)$,
--   $$T_Q\big(H(\rho)/\rho\big)\le(1-\epsilon)\log(1/\rho),\qquad E_\rho(f)\ge H(\rho)\rho^{-\epsilon}.$$
--   In particular, taking $\epsilon=0$ gives $E_\rho(f)\ge H(\rho)$, and hence the Courtade–Kumar inequality $A_\rho(f)\le\Phi(\rho)$, for every $\rho\in[\rho_0,1]$.
--
--   One clock check at $\rho_0$ therefore certifies the inequality on the whole interval $[\rho_0,1]$ for every function in a coefficient cell.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: A_ρ(f) = I(f(X); Y_ρ) in nats → info ρ f = log 2 · mutualInformation ((1 − ρ)/2) f, the mutual information of the published goal (bits, crossover ε = (1 − ρ)/2) converted to nats; reason: the same quantity: flipping each bit with probability (1 − ρ)/2 is the published channel with ε = (1 − ρ)/2, and bits times log 2 are nats
--   - encoding: F⁻¹ : (0, ∞) → (0, ∞), the inverse of the bijection F → Finv y = a chosen v > 0 with F(v) = y (0 when there is none); reason: F is a strictly decreasing bijection of (0, ∞) (Lemma 4.1), so the chosen v is the inverse; the default is never used, since every argument of F⁻¹ here is positive
--   - encoding: the improper integral T(v) = ∫_0^v ds/(s + P(s)) → clock P v = ∫ s in 0..v, 1/(s + P s), an interval (Lebesgue) integral; reason: the integrand is positive, measurable (P is monotone in s, Lemma 4.2) and bounded on (0, v] (P(s) ≥ P(1) > 0 for s ≤ 1, p. 23), so the improper integral equals the Lebesgue integral
--   - encoding: J ≥ 1, weights c_j > 0 and arguments q_j ∈ (0, 1] for j = 1, …, J → c q : Fin J → ℝ with 1 ≤ J, 0 < c j, 0 < q j ≤ 1; reason: index shift only
--   - encoding: “hence the CK inequality, for every ρ ∈ [ρ0, 1]” → ϵ = 0 → ∀ ρ ∈ [ρ0, 1], H(ρ) ≤ E_ρ(f) ∧ A_ρ(f) ≤ Φ(ρ); reason: the CK inequality at ρ is A_ρ(f) ≤ Φ(ρ) (p. 3, (1.3)); both consequences are stated
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 23 (PDF 24), Theorem 4.6

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem theorem_4_6 {n : ℕ} (f : Cube n → Bool) (hW : 0 < levelWeight (signEncoding f) 1)
    {J : ℕ} (hJ : 1 ≤ J) (c q : Fin J → ℝ) (hc : ∀ j, 0 < c j) (hq : ∀ j, 0 < q j ∧ q j ≤ 1)
    (hQP : ∀ y : ℝ, 0 < y → finiteProfile c q y ≤ singletonProfile f y)
    (ρ₀ : ℝ) (hρ₀0 : 0 < ρ₀) (hρ₀1 : ρ₀ < 1) (ϵ : ℝ) (hϵ0 : 0 ≤ ϵ) (hϵ1 : ϵ < 1)
    (hclock : clock (finiteProfile c q) (entropy ρ₀ / ρ₀) ≤ (1 - ϵ) * Real.log (1 / ρ₀)) :
    (∀ ρ : ℝ, ρ₀ ≤ ρ → ρ < 1 →
      clock (finiteProfile c q) (entropy ρ / ρ) ≤ (1 - ϵ) * Real.log (1 / ρ) ∧
        entropy ρ * ρ ^ (-ϵ) ≤ condEntropy ρ f) ∧
    (ϵ = 0 → ∀ ρ : ℝ, ρ₀ ≤ ρ → ρ ≤ 1 → entropy ρ ≤ condEntropy ρ f ∧ info ρ f ≤ Phi ρ) := by sorry

end DictatorsCK.Main
