-- Prove2me | Theorems.Thm_Arxiv2205_09423_mean_reflection_block
-- name    : Arxiv2205_09423.mean_reflection_block
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T12:09:38.234025+00:00
-- url     : https://prove2.me/theorems/3a8708d7-5d99-4868-b28d-2bf9796473bf
-- title:
--   Eq. (21): the mean normalized reflection block
-- statement:
--   Under the hypotheses of the mean transmission formula (Eq. 20), for all modes $i,j$
--
--   $$\langle\bar{\mathbf r}_{(j,i)}\rangle=\delta_{ij}\,\frac{2\pi n\Delta L}{kk_{iz}}\operatorname{sinc}(k_{iz}\Delta L)\,\langle\mathbf A^r_{(j,i)}\rangle,$$
--
--   so only the specular blocks $\mathbf k\to\widetilde{\mathbf k}$ have non-zero mean. Here the particles of a slab of thickness $\Delta L>0$ and density $n>0$ form the ensemble of Section 2.2: the pairs $(\mathbf r_p,\mathbf A_p)$, $p=1,\dots,N$, are independent, each position is independent of the particle's morphology, the amplitude matrices are identically distributed with finite second moments, the $z$ coordinate of each centre is uniform on $[-\Delta L/2,\Delta L/2]$ and independent of its transverse position, and the transverse phase averages obey $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$ for $\mathbf q=\boldsymbol\kappa_i-\boldsymbol\kappa_j-\boldsymbol\kappa_u+\boldsymbol\kappa_v$. $\langle\mathbf A^t_{(j,i)}\rangle$ etc. denote moments of the reduced amplitude matrices of one particle.
--
--   **Formalization Note** The paper obtains its formulas from an infinite slab: it takes the limit $N,V\to\infty$ at fixed $n=N/V$ of $N\langle e^{i\boldsymbol\eta\cdot\mathbf r}\rangle$, gets $(2\pi)^2n\Delta L\operatorname{sinc}(\eta_z\Delta L/2)\delta(\eta_x)\delta(\eta_y)$ (Eq. 19), and then replaces $\delta(\eta_x)\delta(\eta_y)$ by $\delta_{ij}/w$. A uniform law on an infinite slab and this Dirac-to-Kronecker replacement have no rigorous counterpart. The statement therefore keeps $N$ finite and takes the discretized transverse average as a hypothesis on the position law, $N\langle e^{i\mathbf q\cdot\boldsymbol\rho}\rangle=(2\pi)^2n\Delta L\,\delta_{\mathbf q,\mathbf 0}/w$. The $z$ average $\operatorname{sinc}(\eta_z\Delta L/2)$ is derived from the uniform law in $z$. Under these hypotheses the paper's formula holds exactly for finite $N$. The hypothesis is satisfiable for every mode set; at $\mathbf q=\mathbf 0$ it fixes $n=Nw/((2\pi)^2\Delta L)$.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c003; Section 2.2, Eq. (21), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem mean_reflection_block {Nk N : ℕ} (K : ModeSet Nk) (hK : K.IsValid) (dL n : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (r : Fin N → Ω → Fin 3 → ℝ) (A : Fin N → Ω → Amp) (hE : IsSlabEnsemble K dL n P r A)
    (p0 : Fin N)
    (j i : Fin (2 * Nk + 1)) (b a : Fin 2) :
    ∫ ω, rbar K (fun p => A p ω) (fun p => r p ω) j i b a ∂P =
      if i = j then
        ((2 * Real.pi * n * dL / (K.k * K.kz i) * Real.sinc (K.kz i * dL) : ℝ) : ℂ) *
          ∫ ω, ampRed K (A p0 ω) K.kvec K.kvecT j i b a ∂P
      else 0 := by sorry

end Arxiv2205_09423
