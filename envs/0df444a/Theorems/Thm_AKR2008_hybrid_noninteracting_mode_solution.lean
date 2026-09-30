-- Prove2me | Theorems.Thm_AKR2008_hybrid_noninteracting_mode_solution
-- name    : AKR2008.hybrid_noninteracting_mode_solution
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-28T00:31:25.750985+00:00
-- url     : https://prove2.me/theorems/588c2d81-f3ba-4bce-a2b6-7804c6ad4b96
-- title:
--   Sec. IV A: the kernels (49)–(51), (54), (55) solve the non-interacting equations (44)–(48)
-- statement:
--   Consider the non-interacting ($g=0$) two-dimensional Nordström model with a quantized massive scalar field of mass $m$, in the configuration-space-ensemble description of Sec. IV A, with the Gaussian ansatz for $S^c$, $P^c$, $P^q$. Throughout, kernels of Sec. IV A are written in the real orthonormal eigenbasis $f^{(k)}$ of $-\partial_x^2$ (eigenvalue $k^2$): a kernel $A_{xy}=\sum_k A_k f^{(k)}_x f^{(k)}_y$ is represented by its mode coefficient $A_k$, so $\int dx\,A_{yx}B_{xz}\mapsto A_kB_k$, $\partial_z^2\delta(y-z)\mapsto -k^2$ and $\int dx\,A_{xx}\mapsto\sum_k A_k$.
--
--   Let $\{k_i\}_{i\in\iota}$ be a finite family of mode wave numbers, $\tau_i, w_i$ arbitrary real constants, and $t$ a time with $\cos(k_it)\ne0$ for all $i$. Put $F_i(t)=-k_i\tan(k_it)$, $G_i=\sqrt{k_i^2+m^2}$, $K_i(t)=\tau_i/\cos^2(k_it)$, $\beta_i(t)=w_i\cos(k_it)$ and $N^c(t)=1/\prod_i\cos(k_it)$. Then at time $t$:
--
--   1. Eq. (44): $\dot F_i + F_i^2 + k_i^2 = 0$ for every $i$;
--   2. Eq. (45): $-G_i^2 + (k_i^2+m^2) = 0$ for every $i$;
--   3. Eq. (46): $$\frac{\dot N^c}{N^c} - \frac12\,\frac{d}{dt}\Bigl(\sum_i \beta_i K_i \beta_i\Bigr) + \sum_i F_i = 0;$$
--   4. Eq. (47): $\dfrac{d}{dt}(\beta_iK_i) + \beta_iK_iF_i = 0$ for every $i$;
--   5. Eq. (48): $-\tfrac12\dot K_i - K_iF_i = 0$ for every $i$.
--
--   This is the paper's explicit solution of the uncoupled classical-quantum system: the classical gravitational-wave sector is a field-theoretic analogue of a classical oscillator ensemble, and the quantum sector is a one-particle Schrödinger wave functional. It is the $g=0$ starting point of the first-order hybrid solution of Sec. IV B.
--
--   **Formalization Note** The kernel equations are stated mode by mode in the eigenbasis, and the family of modes is finite (a truncation). Eq. (43), which involves the divergent zero-point term $\int dx\,G_{xx}$, and Eq. (53) are not part of this statement.
-- source:
--   M. Albers, C. Kiefer, M. Reginatto, Measurement analysis and quantum gravity, Phys. Rev. D 78, 064051 (2008), https://doi.org/10.1103/PhysRevD.78.064051, p. 064051-10, Sec. IV A, Eqs. (44)–(51), (54), (55)

import Mathlib
import Definitions.Def_AKR2008_HybridDefs

namespace AKR2008

theorem hybrid_noninteracting_mode_solution {ι : Type*} [Fintype ι] (k τ w : ι → ℝ) (m t : ℝ)
    (hcos : ∀ i, Real.cos (k i * t) ≠ 0) :
    (∀ i, deriv (fun s => hybridModeF (k i) s) t + hybridModeF (k i) t ^ 2 + k i ^ 2 = 0) ∧
    (∀ i, -hybridModeG m (k i) ^ 2 + (k i ^ 2 + m ^ 2) = 0) ∧
    (deriv (fun s => hybridNc k s) t / hybridNc k t
        - (1 / 2) * deriv (fun s => ∑ i, hybridModeBeta (w i) (k i) s *
            hybridModeK (τ i) (k i) s * hybridModeBeta (w i) (k i) s) t
        + ∑ i, hybridModeF (k i) t = 0) ∧
    (∀ i, deriv (fun s => hybridModeBeta (w i) (k i) s * hybridModeK (τ i) (k i) s) t
        + hybridModeBeta (w i) (k i) t * hybridModeK (τ i) (k i) t * hybridModeF (k i) t = 0) ∧
    (∀ i, -(1 / 2) * deriv (fun s => hybridModeK (τ i) (k i) s) t
        - hybridModeK (τ i) (k i) t * hybridModeF (k i) t = 0) := by sorry

end AKR2008
