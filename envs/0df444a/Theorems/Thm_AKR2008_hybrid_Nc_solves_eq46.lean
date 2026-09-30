-- Prove2me | Theorems.Thm_AKR2008_hybrid_Nc_solves_eq46
-- name    : AKR2008.hybrid_Nc_solves_eq46
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T23:24:28.43167+00:00
-- url     : https://prove2.me/theorems/2da4c3ab-0930-480b-97d7-2cdb5e515302
-- title:
--   Eq. (55) solves Eq. (46): the normalization $N^c \sim 1/\prod_k\cos(kt)$
-- statement:
--   Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$.
--
--   Let $\{k_i\}_{i\in\iota}$ be a finite family of wave numbers, $\tau_i,w_i$ real constants, and $t$ a time with $\cos(k_it)\ne0$ for all $i$. With $F_i=-k_i\tan(k_it)$ (Eq. (49)), $K_i=\tau_i/\cos^2(k_it)$ (Eq. (51)), $\beta_i=w_i\cos(k_it)$ (Eq. (54)) and $N^c(t)=1/\prod_i\cos(k_it)$ (Eq. (55)), the mode form of Eq. (46) holds:
--   $$\frac{\dot N^c}{N^c} - \frac12\,\frac{d}{dt}\Bigl(\sum_i\beta_iK_i\beta_i\Bigr) + \sum_iF_i = 0 .$$
--
--   Eq. (46) is the part of the continuity equation (42) that fixes the normalization of the classical Gaussian ensemble $P^c$.
--
--   **Formalization Note** The paper writes $N^c\sim1/\prod_k\cos(kt)$ over all modes; the statement uses the representative with constant $1$ and a finite family of modes.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-10, Sec. IV A, Eqs. (46), (49), (51), (54), (55)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem hybrid_Nc_solves_eq46 {ι : Type*} [Fintype ι] (k τ w : ι → ℝ) (t : ℝ)
    (hcos : ∀ i, Real.cos (k i * t) ≠ 0) :
    deriv (fun s => hybridNc k s) t / hybridNc k t
      - (1 / 2) * deriv (fun s => ∑ i, hybridModeBeta (w i) (k i) s *
          hybridModeK (τ i) (k i) s * hybridModeBeta (w i) (k i) s) t
      + ∑ i, hybridModeF (k i) t = 0 := by sorry

end AKR2008
