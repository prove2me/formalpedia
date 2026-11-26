-- Prove2me | Theorems.Thm_Arxiv2205_09423_single_particle_amplitude_rotation
-- name    : Arxiv2205_09423.single_particle_amplitude_rotation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T11:59:54.952043+00:00
-- url     : https://prove2.me/theorems/dcff7779-c94d-4ed9-b1c0-e8d840630db0
-- title:
--   Eq. (D2): the single-particle matrix from the amplitude scattering matrix (as proved)
-- statement:
--   Let $\mathbf e_{ki},\mathbf e_{kj}\in\mathbb R^3$ be unit incident and outgoing directions with $\mathbf e_{kj}\ne-\mathbf e_{ki}$, and let $X$ be a complex $3\times3$ matrix. Let $(\mathbf e_{\theta},\mathbf e_{\phi})$ be the polar bases (11) of the two directions, let $\mathbf e_\perp,\mathbf e_{\parallel i},\mathbf e_{\parallel j}$ be the scattering-plane vectors of Appendix D (with the paper's choice $\mathbf e_{\parallel}=\mathbf e_\theta$, $\mathbf e_\perp=\mathbf e_{\phi i}$ for parallel directions), let $\theta_i,\theta_j$ be the signed angles from $\mathbf e_{\theta}$ to $\mathbf e_{\parallel}$, and let $S_1,\dots,S_4$ be the components of $X$ in the frames $(\mathbf e_\parallel,\mathbf e'_\perp)$, $\mathbf e'_\perp=-\mathbf e_\perp$. Then the reduced matrix $[\mathbf e_m(\mathbf e_{kj})^{\mathrm T}X\mathbf e_n(\mathbf e_{ki})]_{m,n\in\{\theta,\phi\}}$ is
--
--   $$\mathbf R(-\theta_j)\,\boldsymbol\sigma_z\begin{pmatrix}S_2&S_3\\S_4&S_1\end{pmatrix}\boldsymbol\sigma_z\,\mathbf R(\theta_i),\qquad \mathbf R(\theta)=\begin{pmatrix}\cos\theta&\sin\theta\\-\sin\theta&\cos\theta\end{pmatrix}.$$
--
--   Applied to $X=\mathbf A_p(\mathbf u_j,\mathbf u_i)$, this gives $\mathbf A^{t/r}_{(j,i)}$ from the amplitude scattering matrix of a particle.
--
--   **Formalization Note** The paper states Eq. (D2) for every pair of directions. For antiparallel directions ($\mathbf e_{kj}=-\mathbf e_{ki}$, including direct backscattering), the paper's convention $\mathbf e_{\parallel j}=\mathbf e_{\theta j}$, $\mathbf e_\perp=\mathbf e_{\phi i}$ makes $(\mathbf e_{\parallel j},\mathbf e_\perp,\mathbf e_{kj})$ left-handed, contrary to the text, and Eq. (D2) then fails (for $\mathbf e_{ki}=\hat{\mathbf z}$, $\mathbf e_{kj}=-\hat{\mathbf z}$ the two sides differ by a left factor $\boldsymbol\sigma_z$). That case is therefore excluded. The $S_m$ are defined as the components of $X$ in the scattering-plane frames, which is how the paper uses them.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c025; Appendix D, Eqs. (D1)-(D2), PDF p. 26

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem single_particle_amplitude_rotation (X : Fin 3 → Fin 3 → ℂ) (ui uj : Fin 3 → ℝ)
    (hi : dotProduct ui ui = 1) (hj : dotProduct uj uj = 1) (hanti : uj ≠ -ui) :
    reduce X ui uj =
      rotM (-signedAngle (eTheta uj) (eParOut ui uj) uj) * sigmaZ * ampScatPlane X ui uj *
        sigmaZ * rotM (signedAngle (eTheta ui) (eParIn ui uj) ui) := by sorry

end Arxiv2205_09423
