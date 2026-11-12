-- Prove2me | Theorems.Thm_DictatorsCK_Main_theorem_4_5
-- name    : DictatorsCK.Main.theorem_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:41:12.060343+00:00
-- url     : https://prove2.me/theorems/5a2fd45d-bf3c-4cd5-add2-98aa2745a674
-- title:
--   Theorem 4.5 — profile clock $T_{P_f}(E_\rho(f)/\rho)\ge-\log\rho$
-- statement:
--   For every $f:\{-1,1\}^n\to\{-1,1\}$ with $W_1(f)>0$ and every $\rho\in(0,1)$,
--   $$T_{P_f}\big(E_\rho(f)/\rho\big)\ge-\log\rho,$$
--   where $E_\rho(f)=\mathbb E H(T_\rho f)$, $P_f(s)=\sum_iB_s(|\hat f(i)|)$ is the singleton profile and $T_{P_f}(v)=\int_0^v\frac{ds}{s+P_f(s)}$ its clock.
--
--   The clock converts the production bound into an integrated lower bound on conditional entropy: the entropy cannot reach a level faster than the comparison equation $z'=z+P_f(z)$ allows.
--
--   Differences from the source:
--   - encoding: the cube {−1, 1}^n and Boolean f : {−1, 1}^n → {−1, 1} → Cube n = Fin n → Bool with x_i = 1 ⇔ true (coord, signEncoding); a Boolean f is f : Cube n → Bool read through signEncoding (true ↦ 1, false ↦ −1); reason: the cube type of the referenced goal; a relabelling of points and values that changes no instance
--   - encoding: F⁻¹ : (0, ∞) → (0, ∞), the inverse of the bijection F → Finv y = a chosen v > 0 with F(v) = y (0 when there is none); reason: F is a strictly decreasing bijection of (0, ∞) (Lemma 4.1), so the chosen v is the inverse; the default is never used, since every argument of F⁻¹ here is positive
--   - encoding: the improper integral T(v) = ∫_0^v ds/(s + P(s)) → clock P v = ∫ s in 0..v, 1/(s + P s), an interval (Lebesgue) integral; reason: the integrand is positive, measurable (P is monotone in s, Lemma 4.2) and bounded on (0, v] (P(s) ≥ P(1) > 0 for s ≤ 1, p. 23), so the improper integral equals the Lebesgue integral
-- source:
--   Ky, Tran, Dictators are most informative, arXiv:2609.24184 (held copy, sha256 aa2515fb…0a2c7f), p. 22 (PDF 23), Theorem 4.5

import Mathlib
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_DictatorsCK_Main_Fourier
import Definitions.Def_DictatorsCK_Main_Information
import Definitions.Def_DictatorsCK_Main_Profile

open OAI.LeanBlast.CourtadeKumar

namespace DictatorsCK.Main

theorem theorem_4_5 {n : ℕ} (f : Cube n → Bool) (hW : 0 < levelWeight (signEncoding f) 1) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    -Real.log ρ ≤ clock (singletonProfile f) (condEntropy ρ f / ρ) := by sorry

end DictatorsCK.Main
