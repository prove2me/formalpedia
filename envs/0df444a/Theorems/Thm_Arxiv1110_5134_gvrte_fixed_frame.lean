-- Prove2me | Theorems.Thm_Arxiv1110_5134_gvrte_fixed_frame
-- name    : Arxiv1110_5134.gvrte_fixed_frame
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T09:16:06.075799+00:00
-- url     : https://prove2.me/theorems/ee6b7de3-dcc1-4847-9b9d-249febe8f96d
-- title:
--   Eqs. (36)-(39): the GVRTE for Stokes vectors in a fixed reference frame
-- statement:
--   At a point $s$ of a ray, let $n(s)>0$, let $\sigma(s)=(\boldsymbol\Omega\times\boldsymbol\nu)\cdot\mathbf e_z\ne0$, and let the fixed-frame Stokes vector $\mathbf I_G$ be related to the Frenet-frame Stokes vector by $\mathbf I=\tilde\Re(-\phi_G)\mathbf I_G$ (Eq. 32). The same relation $\mathbf I(s,\boldsymbol\Omega')=\tilde\Re(-\phi'_G)\mathbf I_G(s,\boldsymbol\Omega')$ holds for every incident direction $\boldsymbol\Omega'$, where $\phi'_G$ and $\sigma'=(\boldsymbol\Omega'\times\boldsymbol\nu')\cdot\mathbf e_z\ne0$ are the corresponding quantities for $\boldsymbol\Omega'$. Assume $n$, $\mathbf I_G$ and the entries of $\tilde\Re(-\phi_G(s))$ are differentiable in $s$. Suppose $\mathbf I$ satisfies the GVRTE (Eq. 20),
--
--   $$n^2\frac{d}{ds}\Big[\frac{\mathbf I}{n^2}\Big]+(\boldsymbol\kappa_e+\mathbf R)\mathbf I=\boldsymbol\kappa_a\mathbf I_b+\frac1{4\pi}\int_{4\pi}\mathbf Z(\boldsymbol\Omega',\boldsymbol\Omega)\mathbf I(s,\boldsymbol\Omega')\,d\Omega'.$$
--
--   Then $\mathbf I_G$ satisfies (Eq. 38)
--
--   $$n^2\frac{d}{ds}\Big[\frac{\mathbf I_G}{n^2}\Big]+\Big[\tilde\Re(\phi_G)\frac{d\tilde\Re(-\phi_G)}{ds}+(\tilde{\boldsymbol\kappa}_e+\tilde{\mathbf R})\Big]\mathbf I_G=\tilde{\boldsymbol\kappa}_a\mathbf I_{b,G}+\frac1{4\pi}\int_{4\pi}\tilde{\mathbf Z}(\boldsymbol\Omega',\boldsymbol\Omega)\mathbf I_G(s,\boldsymbol\Omega')\,d\Omega',$$
--
--   with the modified properties (Eqs. 39a-d)
--
--   $$\tilde{\boldsymbol\kappa}_e=\tilde\Re(\phi_G)\boldsymbol\kappa_e\tilde\Re(-\phi_G),\quad\tilde{\mathbf R}=\tilde\Re(\phi_G)\mathbf R\tilde\Re(-\phi_G),\quad\tilde{\boldsymbol\kappa}_a=\tilde\Re(\phi_G)\boldsymbol\kappa_a\tilde\Re(-\phi_G),\quad\tilde{\mathbf Z}(\boldsymbol\Omega',\boldsymbol\Omega)=\tilde\Re(\phi_G)\mathbf Z(\boldsymbol\Omega',\boldsymbol\Omega)\tilde\Re(-\phi'_G),$$
--
--   where $\mathbf I_{b,G}=\tilde\Re(\phi_G)\mathbf I_b$.
--
--   **Formalization Note** The statement is at a single point $s$. $\mathbf Z(\cdot,\boldsymbol\Omega)$ and $\mathbf I_G(s,\cdot)$ are arbitrary functions of the incident direction at that point. The emission vector in the fixed frame is $\mathbf I_{b,G}=\tilde\Re(\phi_G)\mathbf I_{b}$, which the paper uses implicitly between Eqs. (36) and (37). The paper's remark that Eq. (38) reduces to the classic VRTE for uniform $n$ is not stated.
-- source:
--   Zhao, Tan and Liu, On the Derivation of Vector Radiative Transfer Equation for Polarized Radiative Transport in Graded Index Media, arXiv:1110.5134v1 (2011), claim c013; Section 4.1, Eqs. (36)-(39d), PDF pp. 17-18

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology
open scoped Matrix

namespace Arxiv1110_5134

theorem gvrte_fixed_frame (n : ℝ → ℝ) (s : ℝ) (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s)
    (σ φG : ℝ → ℝ) (hσ : σ s ≠ 0)
    (hM : ∀ i j, DifferentiableAt ℝ (fun t => modRot (σ t) (-φG t) i j) s)
    (IG : ℝ → Stokes) (hIG : DifferentiableAt ℝ IG s)
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (σ' φG' : Dir → ℝ) (hσ' : ∀ ω, σ' ω ≠ 0)
    (IGin : Dir → Stokes)
    (h20 : transportOp n (fun t => modRot (σ t) (-φG t) *ᵥ IG t) s +
        (κe + rytovMatrix κ) *ᵥ (modRot (σ s) (-φG s) *ᵥ IG s) =
      κa *ᵥ Ib + scatSource Z (fun ω => modRot (σ' ω) (-φG' ω) *ᵥ IGin ω)) :
    transportOp n IG s +
        (modRot (σ s) (φG s) * matDeriv (fun t => modRot (σ t) (-φG t)) s +
          (modRot (σ s) (φG s) * κe * modRot (σ s) (-φG s) +
            modRot (σ s) (φG s) * rytovMatrix κ * modRot (σ s) (-φG s))) *ᵥ IG s =
      (modRot (σ s) (φG s) * κa * modRot (σ s) (-φG s)) *ᵥ (modRot (σ s) (φG s) *ᵥ Ib) +
        scatSource (fun ω => modRot (σ s) (φG s) * Z ω * modRot (σ' ω) (-φG' ω)) IGin := by sorry

end Arxiv1110_5134
