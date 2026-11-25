-- Prove2me | Theorems.Thm_Arxiv2201_05558_small_offset_expansions
-- name    : Arxiv2201_05558.small_offset_expansions
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T11:14:03.793194+00:00
-- url     : https://prove2.me/theorems/c1dbea5c-73e8-4a0c-9aba-781c0aa3d5bf
-- title:
--   Section 5.6: expansions of $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ for $D\Omega z^2/c_o\ll1$
-- statement:
--   Let $\omega_0,c_o,D>0$ and let $a_\Omega,b_\Omega,c_\Omega,d_\Omega$ be the coefficients of Proposition 5.4, with $\Omega\ne0$ and $z>0$. There are constants $M$ and $\delta>0$ such that, whenever $|D\Omega z^2/c_o|<\delta$,
--
--   $$a_\Omega(z)=-i\frac{D\Omega z^2}{8c_o}+\frac{D^2\Omega^2z^4}{192c_o^2}+O\Big(\frac{D^3\Omega^3z^6}{c_o^3}\Big),$$
--
--   $$b_\Omega(z)=\frac{\omega_0^2Dz}{16c_o^2}\Big(1+i\frac{D\Omega z^2}{12c_o}-\frac{D^2\Omega^2z^4}{120c_o^2}+O\Big(\frac{D^3\Omega^3z^6}{c_o^3}\Big)\Big),$$
--
--   $$c_\Omega(z)=\frac{\omega_0Dz^2}{16c_o}\Big(1+i\frac{D\Omega z^2}{16c_o}-\frac{7D^2\Omega^2z^4}{1152c_o^2}+O\Big(\frac{D^3\Omega^3z^6}{c_o^3}\Big)\Big),$$
--
--   $$d_\Omega(z)=\frac{Dz^3}{48}\Big(1+i\frac{3D\Omega z^2}{80c_o}-\frac{3D^2\Omega^2z^4}{896c_o^2}+O\Big(\frac{D^3\Omega^3z^6}{c_o^3}\Big)\Big).$$
--
--   Each $O(\cdot)$ term is bounded in modulus by $M|D\Omega z^2/c_o|^3$.
--
--   **Formalization Note** The paper's "$\simeq$ … $+O(\cdot)$ for $D\Omega z^2/c_o\ll1$" is read as a bound uniform in $(\Omega,z)$ for small $|D\Omega z^2/c_o|$. This reading is exact: each coefficient divided by its prefactor depends on $(\Omega,z)$ only through $s=\sqrt{D|\Omega|/(4c_o)}\,z$, and $D|\Omega|z^2/c_o=4s^2$. $\Omega=0$ is excluded because the formulas of Proposition 5.4 are undefined there.
-- source:
--   Garnier and Sølna, Speckle Memory Effect in the Frequency Domain and Stability in Time-Reversal Experiments, arXiv:2201.05558v1 (2022), claim c013; Section 5.6, Taylor expansions after Figure 5.1, PDF pp. 21-22

import Mathlib
import Definitions.Def_Arxiv2201_05558_Basic

open MeasureTheory Filter Topology

namespace Arxiv2201_05558

theorem small_offset_expansions (ω0 c0 D : ℝ) (hω0 : 0 < ω0) (hc0 : 0 < c0) (hD : 0 < D) :
    ∃ M δ : ℝ, 0 < δ ∧ ∀ Ω z : ℝ, Ω ≠ 0 → 0 < z → |D * Ω * z ^ 2 / c0| < δ →
      ‖aOm c0 D (fun _ => 0) Ω z -
          (-(Complex.I * (D * Ω * z ^ 2 / (8 * c0) : ℝ)) +
            (D ^ 2 * Ω ^ 2 * z ^ 4 / (192 * c0 ^ 2) : ℝ))‖ ≤
        M * |D * Ω * z ^ 2 / c0| ^ 3 ∧
      ‖bOm ω0 c0 D (fun _ => 0) Ω z -
          (ω0 ^ 2 * D * z / (16 * c0 ^ 2) : ℝ) *
            (1 + Complex.I * (D * Ω * z ^ 2 / (12 * c0) : ℝ) -
              (D ^ 2 * Ω ^ 2 * z ^ 4 / (120 * c0 ^ 2) : ℝ))‖ ≤
        M * (ω0 ^ 2 * D * z / (16 * c0 ^ 2)) * |D * Ω * z ^ 2 / c0| ^ 3 ∧
      ‖cOm ω0 c0 D (fun _ => 0) Ω z -
          (ω0 * D * z ^ 2 / (16 * c0) : ℝ) *
            (1 + Complex.I * (D * Ω * z ^ 2 / (16 * c0) : ℝ) -
              (7 * D ^ 2 * Ω ^ 2 * z ^ 4 / (1152 * c0 ^ 2) : ℝ))‖ ≤
        M * (ω0 * D * z ^ 2 / (16 * c0)) * |D * Ω * z ^ 2 / c0| ^ 3 ∧
      ‖dOm c0 D (fun _ => 0) Ω z -
          (D * z ^ 3 / 48 : ℝ) *
            (1 + Complex.I * (3 * D * Ω * z ^ 2 / (80 * c0) : ℝ) -
              (3 * D ^ 2 * Ω ^ 2 * z ^ 4 / (896 * c0 ^ 2) : ℝ))‖ ≤
        M * (D * z ^ 3 / 48) * |D * Ω * z ^ 2 / c0| ^ 3 := by sorry

end Arxiv2201_05558
