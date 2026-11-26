-- Prove2me | Theorems.Thm_Arxiv1803_10134_quasi_mode_time_response
-- name    : Arxiv1803_10134.quasi_mode_time_response
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-26T13:11:18.202073+00:00
-- url     : https://prove2.me/theorems/91a6d700-427e-4803-bd73-847ed0d7a327
-- title:
--   Eq. (18): decaying quasi-modes of the pulse response (as derived)
-- statement:
--   Let $\rho_0,c_p,c_s,\omega_0,\Gamma_0>0$, let $\mathbf r_1,\dots,\mathbf r_N$ be pairwise distinct, and let $\Lambda_n,|R_n\rangle,\langle L_n|$ be a biorthogonal eigensystem of $\hat G(\omega_0)$ (eqs. 13–15). Consider a short pulse $|v(t)\rangle=|v\rangle\delta(t)$, whose Fourier transform is the constant vector $|v\rangle$. Let $|u(\omega)\rangle$ solve, for every real $\omega\neq0$,
--   $$|u(\omega)\rangle=|v\rangle+\frac{\alpha_0(\omega)}{B}\big[\hat G(\omega_0)-i\mathbb 1\big]|u(\omega)\rangle.$$
--   Then:
--
--   1. Every quasi-mode decays: $\Gamma_n=\Gamma_0\operatorname{Im}\Lambda_n>0$ for all $n$.
--   2. For every $t>0$, the response $|u(t)\rangle=\frac1{2\pi}\int|u(\omega)\rangle e^{-i\omega t}\,d\omega$, taken as $\lim_{T\to\infty}\frac1{2\pi}\int_{-T}^{T}e^{-i\omega t}\big(|u(\omega)\rangle-|v\rangle\big)\,d\omega$, equals
--   $$|u(t)\rangle=\sum_nA_n(t)|R_n\rangle,\qquad A_n(t)=\frac{\Gamma_0}{2}(1+i\Lambda_n)\langle L_n|v\rangle\,e^{-i\omega_nt-\Gamma_nt/2}.$$
--
--   So $A_n(t)\propto\exp(-i\omega_nt-\Gamma_nt/2)$: the $|R_n\rangle$ are quasi-modes with frequencies $\omega_n$ and decay rates $\Gamma_n$.
--
--   **Formalization Note** The paper writes only "$A_n(t)\propto\exp(-i\omega_nt-\Gamma_nt/2)$". The statement gives the exact coefficient for $t>0$, which the computation yields without neglecting any $\omega$-dependence. The incident term $|v\rangle$, whose transform is $|v\rangle\delta(t)$ and vanishes for $t>0$, is subtracted so that the Fourier integral converges as an improper integral. The decay $\Gamma_n>0$, which the paper attributes to the openness of the system, is part of the conclusion, not a hypothesis. Fourier convention: $e^{-i\omega t}$, as eq. (18) requires.
-- source:
--   Skipetrov and Beltukov, Anderson transition for elastic waves in three dimensions, arXiv:1803.10134v3 (2018), claim c009; Section III A, eq. (18) with eqs. (11), (13)-(17), PDF p. 5

import Mathlib
import Definitions.Def_Arxiv1803_10134_Basic

open Complex MeasureTheory Filter Topology

namespace Arxiv1803_10134

theorem quasi_mode_time_response {N : ℕ} (rho0 cp cs om0 gam0 : ℝ) (hrho0 : 0 < rho0)
    (hcp : 0 < cp) (hcs : 0 < cs) (hom0 : 0 < om0) (hgam0 : 0 < gam0)
    (r : Fin N → Space) (hr : Function.Injective r)
    (lam : Idx N → ℂ) (R L : Idx N → Idx N → ℂ)
    (hRL : IsBiorthogonalEigensystem (greenMatrix rho0 cp cs om0 r) lam R L)
    (v : Idx N → ℂ) (u : ℝ → Idx N → ℂ)
    (hu : ∀ om : ℝ, om ≠ 0 → u om = v + (polarizability (prefactorB rho0 cp cs om) om0 gam0 om /
          (prefactorB rho0 cp cs om : ℂ)) •
        (greenMatrix rho0 cp cs om0 r - I • (1 : Matrix (Idx N) (Idx N) ℂ)).mulVec (u om)) :
    (∀ n, 0 < qmWidth gam0 (lam n)) ∧
    ∀ t : ℝ, 0 < t →
      Tendsto (fun T : ℝ => ((2 * Real.pi : ℝ) : ℂ)⁻¹ •
          ∫ om in (-T)..T, cexp (-(I * (om : ℂ) * (t : ℂ))) • (u om - v)) atTop
        (𝓝 (∑ n, (((gam0 / 2 : ℝ) : ℂ) * (1 + I * lam n) * (L n ⬝ᵥ v) *
          cexp (-(I * (qmFreq om0 gam0 (lam n) : ℂ) * (t : ℂ)) -
            ((qmWidth gam0 (lam n) / 2 : ℝ) : ℂ) * (t : ℂ))) • R n)) := by sorry

end Arxiv1803_10134
