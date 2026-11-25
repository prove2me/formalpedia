-- Prove2me | Theorems.Thm_Arxiv2201_05558_large_offset_asymptotics
-- name    : Arxiv2201_05558.large_offset_asymptotics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:21:59.002925+00:00
-- url     : https://prove2.me/theorems/7c7cf18b-51da-4bfe-8adb-4ad21a6469d1
-- title:
--   Section 5.6: asymptotics of $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ for $D\Omega z^2/c_o\gg1$
-- statement:
--   Let $\omega_0,c_o,D>0$ and let $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ be the coefficients of Proposition 5.4 for $\Omega>0$, $z>0$. Set $\varepsilon=\exp(-\sqrt{D\Omega/(8c_o)}\,z)$. There are constants $M,S$ such that, whenever $D\Omega z^2/c_o>S$,
--
--   $$a_\Omega(z)\simeq e^{-i\pi/4}\sqrt{\frac{D\Omega}{4c_o}}z-\ln2,\qquad b_\Omega(z)\simeq e^{i\pi/4}\sqrt{\frac{\omega_0^4D}{64c_o^3\Omega}},$$
--
--   $$c_\Omega(z)\simeq e^{i\pi/4}\sqrt{\frac{\omega_0^2D}{16c_o\Omega}}z-\frac{i\omega_0}{2\Omega},\qquad d_\Omega(z)\simeq e^{i\pi/4}\sqrt{\frac{c_oD}{64\Omega}}z^2-\frac{ic_oz}{4\Omega}-e^{3i\pi/4}\sqrt{\frac{c_o^3}{4D\Omega^3}},$$
--
--   where each $\simeq$ means $|\text{exact}-\text{approximation}|\le M\,\varepsilon\,|\text{approximation}|$, i.e. the error is of relative order $\varepsilon$. Moreover
--
--   $$\int_0^\infty\Big(2(s-1)\big[s\tanh s-s+\cosh(s)^{-1}\big]+\big[s\tanh s-s+\cosh(s)^{-1}\big]^2\Big)ds=1,$$
--
--   the identity the paper uses to compute the $O(1)$ term of $d_\Omega$.
--
--   **Formalization Note** "Up to terms of relative order $\varepsilon$" is read as the relative error bound above, uniform for $D\Omega z^2/c_o$ large. The printed integrand is $2(s-1)[s(\tanh(s)-s+\cosh^{-1}(s)]+[s(\tanh(s)-s+\cosh^{-1}(s)]^2$, with unbalanced brackets. It is read as $X=s\tanh s-s+1/\cosh s$, the reading that gives the printed constant in $d_\Omega$. The asymptotics of $a_\Omega$ use the continuous determination of $\ln\cosh$; with the principal logarithm the imaginary part would differ by multiples of $2\pi$.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c014; Section 5.6, large-offset asymptotics after Figure 5.1, PDF p. 22

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem large_offset_asymptotics (ω0 c0 D : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0) (hD : 0 < D) :
    (∃ M S : ℝ, ∀ Ω z : ℝ, 0 < Ω → 0 < z → S < D * Ω * z ^ 2 / c0 →
      ‖aOm c0 D (fun _ => 0) Ω z -
          (eMinusQuarter * (Real.sqrt (D * Ω / (4 * c0)) * z : ℝ) - (Real.log 2 : ℂ))‖ ≤
        M * Real.exp (-(Real.sqrt (D * Ω / (8 * c0)) * z)) *
          ‖eMinusQuarter * (Real.sqrt (D * Ω / (4 * c0)) * z : ℝ) - (Real.log 2 : ℂ)‖ ∧
      ‖bOm ω0 c0 D (fun _ => 0) Ω z -
          Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            (Real.sqrt (ω0 ^ 4 * D / (64 * c0 ^ 3 * Ω)) : ℂ)‖ ≤
        M * Real.exp (-(Real.sqrt (D * Ω / (8 * c0)) * z)) *
          ‖Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
            (Real.sqrt (ω0 ^ 4 * D / (64 * c0 ^ 3 * Ω)) : ℂ)‖ ∧
      ‖cOm ω0 c0 D (fun _ => 0) Ω z -
          (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (ω0 ^ 2 * D / (16 * c0 * Ω)) * z : ℝ) -
            Complex.I * (ω0 / (2 * Ω) : ℝ))‖ ≤
        M * Real.exp (-(Real.sqrt (D * Ω / (8 * c0)) * z)) *
          ‖Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (ω0 ^ 2 * D / (16 * c0 * Ω)) * z : ℝ) -
            Complex.I * (ω0 / (2 * Ω) : ℝ)‖ ∧
      ‖dOm c0 D (fun _ => 0) Ω z -
          (Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (c0 * D / (64 * Ω)) * z ^ 2 : ℝ) -
            Complex.I * (c0 * z / (4 * Ω) : ℝ) -
            Complex.exp (((3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (c0 ^ 3 / (4 * D * Ω ^ 3)) : ℂ))‖ ≤
        M * Real.exp (-(Real.sqrt (D * Ω / (8 * c0)) * z)) *
          ‖Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (c0 * D / (64 * Ω)) * z ^ 2 : ℝ) -
            Complex.I * (c0 * z / (4 * Ω) : ℝ) -
            Complex.exp (((3 * Real.pi / 4 : ℝ) : ℂ) * Complex.I) *
              (Real.sqrt (c0 ^ 3 / (4 * D * Ω ^ 3)) : ℂ)‖) ∧
    ∫ s in Set.Ioi (0 : ℝ),
        (2 * (s - 1) * (s * Real.tanh s - s + (Real.cosh s)⁻¹) +
          (s * Real.tanh s - s + (Real.cosh s)⁻¹) ^ 2) = 1 := by sorry

end Arxiv2201_05558
