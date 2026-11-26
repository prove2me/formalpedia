-- Prove2me | Theorems.Thm_Arxiv2205_09423_transmission_covariance_offdiagonal
-- name    : Arxiv2205_09423.transmission_covariance_offdiagonal
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T12:14:25.938137+00:00
-- url     : https://prove2.me/theorems/5878fde3-7df9-4868-bd35-437ff4909b24
-- title:
--   Eq. (25): covariance of off-diagonal transmission blocks (memory effect)
-- statement:
--   Under the hypotheses of the mean transmission formula (Eq. 20), let $i\ne j$ and $u\ne v$ be modes and $a,b,c,d\in\{\theta,\phi\}$. Then
--
--   $$\langle\bar t_{(j,i)ba}\bar t^*_{(v,u)dc}\rangle-\langle\bar t_{(j,i)ba}\rangle\langle\bar t^*_{(v,u)dc}\rangle=\delta^R C_{ijuv}\langle A^t_{(j,i)ba}A^{t*}_{(v,u)dc}\rangle\operatorname{sinc}\Big(\frac{\Delta L}{2}(k_{iz}-k_{jz}-k_{uz}+k_{vz})\Big),$$
--
--   where $C_{ijuv}=wn\Delta L/(k^2\sqrt{k_{iz}k_{jz}k_{uz}k_{vz}})$ and $\delta^R=1$ if $k_{ix}-k_{jx}=k_{ux}-k_{vx}$ and $k_{iy}-k_{jy}=k_{uy}-k_{vy}$ (the memory-effect condition, Eq. 24), $\delta^R=0$ otherwise. Here the particles of a slab of thickness $\Delta L>0$ and density $n>0$ form the ensemble of Section 2.2: the pairs $(\mathbf r_p,\mathbf A_p)$, $p=1,\dots,N$, are independent, each position is independent of the particle's morphology, the amplitude matrices are identically distributed with finite second moments, the $z$ coordinate of each centre is uniform on $[-\Delta L/2,\Delta L/2]$ and independent of its transverse position, and the transverse phase averages obey $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$ for $\mathbf q=\boldsymbol\kappa_i-\boldsymbol\kappa_j-\boldsymbol\kappa_u+\boldsymbol\kappa_v$. $\langle\mathbf A^t_{(j,i)}\rangle$ etc. denote moments of the reduced amplitude matrices of one particle.
--
--   **Formalization Note** The paper obtains its formulas from an infinite slab: it takes the limit $N,V\to\infty$ at fixed $n=N/V$ of $N\langle e^{i\boldsymbol\eta\cdot\mathbf r}\rangle$, gets $(2\pi)^2n\Delta L\operatorname{sinc}(\eta_z\Delta L/2)\delta(\eta_x)\delta(\eta_y)$ (Eq. 19), and then replaces $\delta(\eta_x)\delta(\eta_y)$ by $\delta_{ij}/w$. A uniform law on an infinite slab and this Dirac-to-Kronecker replacement have no rigorous counterpart. The statement therefore keeps $N$ finite and takes the discretized transverse average as a hypothesis on the position law, $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$. The $z$ average $\operatorname{sinc}(\eta_z\Delta L/2)$ is derived from the uniform law in $z$. Under these hypotheses the paper's formula holds exactly for finite $N$. The hypothesis is satisfiable for every mode set; at $\mathbf q=\mathbf 0$ it fixes $n=Nw/((2\pi)^2\Delta L)$. In the paper, the terms with two different particles reduce to the product of means only as $N\to\infty$. Here that product is exactly $0$ for off-diagonal blocks, so no limit is needed.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c004; Section 2.2, Eqs. (22)-(25), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem transmission_covariance_offdiagonal {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i v u : Fin (2 * Nk + 1)) (hij : i ≠ j) (huv : u ≠ v) (b a d c : Fin 2) :
    covC P (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) j i b a)
        (fun ω => tbar K (fun p => A p ω) (fun p => r p ω) v u d c) =
      ((K.deltaR i j u v * K.cijuv n dL i j u v *
          Real.sinc (dL / 2 * (K.kz i - K.kz j - K.kz u + K.kz v)) : ℝ) : ℂ) *
        ∫ ω, ampRed K (A p0 ω) K.kvec K.kvec j i b a *
          star (ampRed K (A p0 ω) K.kvec K.kvec v u d c) ∂P := by sorry

end Arxiv2205_09423
