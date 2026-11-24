-- Prove2me | Theorems.Thm_Arxiv1110_5134_gvrte_nonparticipating
-- name    : Arxiv1110_5134.gvrte_nonparticipating
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:04:14.3349+00:00
-- url     : https://prove2.me/theorems/56638272-a307-4dfb-8da5-9196c815b7f1
-- title:
--   Eqs. (13)-(14): the GVRTE for non-participating graded index media
-- statement:
--   Consider a ray in a non-participating graded index medium, with arc length $s$, refractive index $n(s)>0$ and torsion $\kappa$. The beam has intensity $I$, ellipticity angle $\chi$ and orientation angle $\psi$, measured in the Frenet-Serret frame $\boldsymbol\nu,\mathbf b,\boldsymbol\Omega$ of the ray. Assume:
--
--   - the Clausius invariant $\frac{d}{ds}[I/n^2]=0$ (Eq. 3);
--   - the ellipticity angle is conserved, $d\chi/ds=0$;
--   - Rytov's law $d\psi/ds=\kappa$ (Eq. 2).
--
--   Then the Stokes vector $\mathbf I=(I,Q,U,V)$ of Eq. (1) satisfies the vector radiative transfer equation for non-participating graded index media (Eq. 13)
--
--   $$n^2\frac{d}{ds}\Big[\frac{\mathbf I}{n^2}\Big]+\mathbf R\,\mathbf I=0,\qquad \mathbf R=\begin{pmatrix}0&0&0&0\\0&0&2\kappa&0\\0&-2\kappa&0&0\\0&0&0&0\end{pmatrix}\quad\text{(Eq. 14)}.$$
--
--   Its first component is the Clausius invariant. The torsion couples only $Q$ and $U$.
--
--   **Formalization Note** The statement is at a single point $s$ of the ray, with $\kappa$ the torsion there. It also asserts that $\mathbf I/n^2$ is differentiable at $s$, so the derivative in Eq. (13) is a genuine derivative.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c005; Section 3.1, Eqs. (13)-(14), PDF p. 10

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem gvrte_nonparticipating (n I χ ψ : ℝ → ℝ) (κ s : ℝ) (hn : 0 < n s)
    (hI : HasDerivAt (fun t => I t / n t ^ 2) 0 s) (hχ : HasDerivAt χ 0 s)
    (hψ : HasDerivAt ψ κ s) :
    DifferentiableAt ℝ (fun t => (n t ^ 2)⁻¹ • stokesVec (I t) (χ t) (ψ t)) s ∧
    transportOp n (fun t => stokesVec (I t) (χ t) (ψ t)) s +
      rytovMatrix κ *ᵥ stokesVec (I s) (χ s) (ψ s) = 0 := by sorry

end Arxiv1110_5134
