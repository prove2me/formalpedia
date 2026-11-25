-- Prove2me | Theorems.Thm_Arxiv1901_08703_rellich_upper_half_plane
-- name    : Arxiv1901_08703.rellich_upper_half_plane
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:23:59.998532+00:00
-- url     : https://prove2.me/theorems/5fa17eba-7166-4022-a087-457dcc00c7ed
-- title:
--   Lemma 4.1: Rellich's lemma in the upper half-plane with a flat Neumann boundary
-- statement:
--   Let $k>0$ and $R>0$. Assume that $u^s\in H^1_{loc}(\mathbb R^2_+\setminus\overline{B_R})$ satisfies the Helmholtz equation $\Delta u^s+k^2u^s=0$ in $\mathbb R^2_+\setminus\overline{B_R}$, the Sommerfeld radiation condition (1.3), and the Neumann condition $\partial u^s/\partial\nu=0$ on the flat part $\Gamma\setminus\overline{\Gamma_R}=\{(x_1,0):|x_1|>R\}$. Assume further that the far-field pattern $u^\infty$ of $u^s$ vanishes on $\mathbb S^1_+$. Then $u^s=0$ in $\mathbb R^2_+\setminus\overline{B_R}$.
--
--   **Formalization Note** The Neumann condition is imposed weakly: $\int_{\mathbb R^2_+\setminus\overline{B_R}}(\nabla u^s\cdot\nabla\varphi-k^2u^s\varphi)\,dx=0$ for every $\varphi\in C_c^\infty(\mathbb R^2)$ whose support does not meet $\overline{B_R}$. The hypothesis $u^s\in H^1_{loc}(\mathbb R^2_+\setminus\overline{B_R})$ is taken up to the whole boundary: $\int_{(\mathbb R^2_+\setminus\overline{B_R})\cap B_\rho}(|u^s|^2+|\nabla u^s|^2)\,dx<\infty$ for every $\rho$, so square integrability holds up to the flat part and up to the arc $|x|=R$. This is the paper's usage of $H^1_{loc}$ for $D_+$ and is slightly stronger than an interior reading. "The far-field pattern vanishes on $\mathbb S^1_+$" is the statement $u^s(x)=O(|x|^{-3/2})$ uniformly for $x/|x|\in\mathbb S^1_+$.
-- source:
--   Qu, Zhang and Zhang, A novel integral equation for scattering by locally rough surfaces and application to the inverse problem: the Neumann case, arXiv:1901.08703v1 (2019), claim c013; Section 4, Lemma 4.1, PDF p. 18

import Mathlib
import Definitions.Def_Arxiv1901_08703_Basic

open MeasureTheory

namespace Arxiv1901_08703

theorem rellich_upper_half_plane (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 < R) (u : R2 → ℂ)
    (hH : IsHelmholtzOn (upperExt R) k u) (hH1 : IsH1Loc (upperExt R) u)
    (hrad : IsRadiating k (upperExt R) u) (hN : IsFlatNeumannWeak k R u)
    (hF : HasFarFieldOn k u (fun _ => 0) upperCircle) :
    ∀ x ∈ upperExt R, u x = 0 := by sorry

end Arxiv1901_08703
