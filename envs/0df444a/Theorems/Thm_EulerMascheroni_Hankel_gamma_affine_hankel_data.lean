-- Prove2me | Theorems.Thm_EulerMascheroni_Hankel_gamma_affine_hankel_data
-- name    : EulerMascheroni.Hankel.gamma_affine_hankel_data
-- status  : Open
-- author  : @shivm
-- created : 2026-10-04T14:10:26.373098+00:00
-- url     : https://prove2.me/theorems/28f12591-b7af-4d47-ba80-66e2612e24c4
-- title:
--   Fauzan-type Hankel data for $\gamma$
-- statement:
--   There are $D$, sizes $h_n\le Dn$, rationals $a_{n,k},b_{n,k}$, normalizers $m_n>0$ and $\kappa>0$, $A+U<0$ such that, with $H_n=(a_{n,i+j}+b_{n,i+j}X)_{i,j<h_n}$ and $\Delta_n=\det H_n\in\mathbb Q[X]$, for all large $n$:
--
--   - $H_n(\gamma)$ is positive definite;
--   - $m_n\Delta_n\in\mathbb Z[X]$;
--   - $\log m_n\le(A+\varepsilon)(\kappa n)^2$ and $\log\Delta_n(\gamma)\le(U+\varepsilon)(\kappa n)^2$ for each $\varepsilon>0$.
--
--   This is Fauzan's $\zeta(5)$ scheme with $\gamma$ in place of $\zeta(5)$. The case $h_n=1$ is the classical linear-form approach.
--
--   The known obstruction: the natural positive weight $w(y)=y/(e^{2\pi y}-1)$ (Binet) has rational moments, but its pole values are $\int_0^\infty\frac{w(y)}{y^2+j^2}dy=\tfrac12(\log j-\tfrac1{2j}-H_{j-1}+\gamma)$, which carry $\log j$. So a new weight or functional with values in $\mathbb Q+\mathbb Q\gamma$ is needed.
-- source:
--   A. Fauzan, ζ(5) is irrational (2026), https://zenodo.org/records/22826419, §2 (eqs. (2.2)–(2.5), Prop. 2.2), §§3–6 (normalization and real bound), with γ in place of ζ(5). Binet's second formula: DLMF 5.9.13.

import Mathlib
import Definitions.Def_eulerMascheroni_hankelAffine

open Polynomial Filter Topology

namespace EulerMascheroni.Hankel

theorem gamma_affine_hankel_data :
    ∃ (D : ℕ) (h : ℕ → ℕ) (a b : ℕ → ℕ → ℚ) (m : ℕ → ℚ) (κ A U : ℝ),
      0 < κ ∧ A + U < 0 ∧ (∀ n, h n ≤ D * n) ∧ (∀ n, 0 < m n) ∧
      (∀ᶠ n in atTop, ((hankelAffine (h n) (a n) (b n)).map
          (fun p => aeval Real.eulerMascheroniConstant p)).PosDef) ∧
      (∀ᶠ n in atTop, ∃ Q : ℤ[X],
          Q.map (Int.castRingHom ℚ) = C (m n) * (hankelAffine (h n) (a n) (b n)).det) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          Real.log (m n) ≤ (A + ε) * (κ * (n : ℝ)) ^ 2) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          Real.log (aeval Real.eulerMascheroniConstant (hankelAffine (h n) (a n) (b n)).det)
            ≤ (U + ε) * (κ * (n : ℝ)) ^ 2) := by sorry

end EulerMascheroni.Hankel
