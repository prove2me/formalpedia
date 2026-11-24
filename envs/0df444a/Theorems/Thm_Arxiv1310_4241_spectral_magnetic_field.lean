-- Prove2me | Theorems.Thm_Arxiv1310_4241_spectral_magnetic_field
-- name    : Arxiv1310_4241.spectral_magnetic_field
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T11:22:08.587307+00:00
-- url     : https://prove2.me/theorems/5bafdfb5-fc26-4ade-8085-229641338bdf
-- title:
--   Eqs. (25)-(26): the magnetic field of a current below the plane as attenuated transverse Fourier transforms
-- statement:
--   Let $k=\omega\sqrt{\varepsilon\mu}$ with $\operatorname{Re}k>0$, $\operatorname{Im}k\ge0$, and let $\beta=\sqrt{\xi^2+\eta^2-k^2}$ with the branch of the Sommerfeld formula (9). Let $\mathbf J$ be a continuous current with compact support contained in the lower half-space $z<0$, and let $\mathbf H=\nabla\times\int g_k(\mathbf x-\mathbf x')\mathbf J(\mathbf x')\,dV'$ be its Lorenz-gauge magnetic field (eq. (6)). Then at every point $\mathbf x$ with $z>0$,
--
--   $$\mathbf H(\mathbf x)=\nabla\times\int_{\mathbb R^2}\widehat g_k(\xi,\eta,z)\Big(\int e^{\beta z'}\mathbf J(\mathbf x')e^{-i(\xi x'+\eta y')}\,dV'\Big)e^{i(\xi x+\eta y)}\,d\xi\,d\eta,$$
--
--   and
--
--   $$H_z(\mathbf x)=\int_{\mathbb R^2}\widehat g_k(\xi,\eta,z)\Big(\int e^{\beta z'}\big[i\xi J_y(\mathbf x')-i\eta J_x(\mathbf x')\big]e^{-i(\xi x'+\eta y')}\,dV'\Big)e^{i(\xi x+\eta y)}\,d\xi\,d\eta.$$
--
--   The field above the plane is a superposition of attenuated transverse Fourier transforms of the current.
--
--   **Formalization Note** "Supported in a volume $V$ in the lower half-space" is stated as compact support inside $z<0$; the volume integrals run over all of $\mathbb R^3$.
-- source:
--   M. O'Neil, A generalized Debye source approach to electromagnetic scattering in layered media, arXiv:1310.4241v1 (2013), claim c004; Section IV, eqs. (25) and (26), PDF p. 8; Sommerfeld formula eqs. (9)-(10), PDF p. 4; Lorenz gauge eq. (6), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1310_4241_Basic

open MeasureTheory Filter Topology

namespace Arxiv1310_4241

theorem spectral_magnetic_field (ω : ℝ) (ε μ k : ℂ) (hkdef : k = wavenumber ω ε μ)
    (hk : IsCausalWavenumber k) (J : Space → Fin 3 → ℂ) (hJ : Continuous J)
    (hJc : HasCompactSupport J) (hJV : tsupport J ⊆ {q : Space | q 2 < 0})
    (p : Space) (hp : 0 < p 2) :
    lorenzH k J p = curl (fun p' i => ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p' 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) * J q i *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p' 0) (p' 1)) p ∧
    lorenzH k J p 2 = ∫ ζ : ℝ × ℝ, ghat k ζ.1 ζ.2 (p 2) *
        (∫ q : Space, Complex.exp (sommerfeldRoot k ζ.1 ζ.2 * q 2) *
          (Complex.I * ζ.1 * J q 1 - Complex.I * ζ.2 * J q 0) *
          Complex.exp (-(Complex.I * (ζ.1 * q 0 + ζ.2 * q 1)))) *
        planeWave ζ.1 ζ.2 (p 0) (p 1) := by sorry

end Arxiv1310_4241
