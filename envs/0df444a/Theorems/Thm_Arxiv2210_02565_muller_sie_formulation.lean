-- Prove2me | Theorems.Thm_Arxiv2210_02565_muller_sie_formulation
-- name    : Arxiv2210_02565.muller_sie_formulation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T12:54:48.009335+00:00
-- url     : https://prove2.me/theorems/1e07cfda-c979-46fd-8193-162009bc31d9
-- title:
--   Sec. IV, eqs. (13)-(19): the indirect Müller representation and its second-kind integral equation
-- statement:
--   Let $\omega>0$, let $\epsilon_j,\mu_j,k_j\in\mathbb C$ with $k_j^2=\omega^2\mu_j\epsilon_j$ ($j=1,2$), and let $\mathcal S_j,\mathcal D_j$ be the off-surface potentials (11)-(12), with $\nabla\times\mathcal S_j=\mathcal D_j$ and $\nabla\times\mathcal D_j=k_j^2\mathcal S_j$. Suppose the jump relations (14) hold with $\hat{\mathbf n}$ directed from $\Omega_2$ into $\Omega_1$ (the $+$ side): $\hat{\mathbf n}\times(\mathcal S_1\boldsymbol\varphi)|_+=\mathcal T_1\boldsymbol\varphi$, $\hat{\mathbf n}\times(\mathcal D_1\boldsymbol\varphi)|_+=\mathcal K_1\boldsymbol\varphi+\tfrac12\boldsymbol\varphi$, $\hat{\mathbf n}\times(\mathcal S_2\boldsymbol\varphi)|_-=\mathcal T_2\boldsymbol\varphi$, $\hat{\mathbf n}\times(\mathcal D_2\boldsymbol\varphi)|_-=\mathcal K_2\boldsymbol\varphi-\tfrac12\boldsymbol\varphi$. For currents $\mathbf u,\mathbf v$ define the fields by the Müller representation (13),
--
--   $$\mathbf E_j=k_j^2\mathcal S_j\mathbf v+i\omega\mu_j\mathcal D_j\mathbf u,\qquad \mathbf H_j=k_j^2\mathcal S_j\mathbf u-i\omega\epsilon_j\mathcal D_j\mathbf v.$$
--
--   Then:
--
--   1. $(\mathbf E_j,\mathbf H_j)$ satisfy Maxwell's equations (2): $\nabla\times\mathbf E_j-i\omega\mu_j\mathbf H_j=\mathbf 0$ and $\nabla\times\mathbf H_j+i\omega\epsilon_j\mathbf E_j=\mathbf 0$, for $j=1,2$.
--   2. The jump conditions (4), $\hat{\mathbf n}\times(\mathbf E_2|_--\mathbf E_1|_+)=\mathbf M^{\rm src}$ and $\hat{\mathbf n}\times(\mathbf H_2|_--\mathbf H_1|_+)=\mathbf J^{\rm src}$, hold if and only if $(\mathbf u,\mathbf v)$ solves the second-kind integral equation (18)
--   $$\frac{i\omega}{2}\begin{bmatrix}-(\mu_1+\mu_2)\mathbf u\\(\epsilon_1+\epsilon_2)\mathbf v\end{bmatrix}+\mathsf T\begin{bmatrix}\mathbf u\\\mathbf v\end{bmatrix}=\begin{bmatrix}\mathbf M^{\rm src}\\\mathbf J^{\rm src}\end{bmatrix},\qquad \mathsf T=\begin{bmatrix}i\omega(\mu_2\mathcal K_2-\mu_1\mathcal K_1)&k_2^2\mathcal T_2-k_1^2\mathcal T_1\\k_2^2\mathcal T_2-k_1^2\mathcal T_1&-i\omega(\epsilon_2\mathcal K_2-\epsilon_1\mathcal K_1)\end{bmatrix}.$$
--
--   This is the formulation the windowed Green function method truncates. The strongly singular operators $\mathcal T_j$ enter only through $k_2^2\mathcal T_2-k_1^2\mathcal T_1$.
--
--   **Formalization Note** The surface integrals over the unbounded $\Gamma$ are only conditionally convergent (Section IV), so the potentials, boundary operators, curl and one-sided traces are linear maps on abstract complex vector spaces of currents ($V$) and fields ($W$). The identities $\nabla\times\mathcal S_j=\mathcal D_j$, $\nabla\times\mathcal D_j=k_j^2\mathcal S_j$ and the jump relations (14), which the paper uses without proof, are hypotheses. Only the sides of (14) that enter (4) are assumed. The trace of (13) is taken as the corresponding linear combination of the traces of $\mathcal S_j$ and $\mathcal D_j$. The paper says that enforcing (4) "yields" (18); since (18) is obtained from (4) by an invertible rearrangement, the Lean statement records both directions.
-- source:
--   Arrieta and Pérez-Arancibia, Windowed Green Function MoM for Second-Kind Surface Integral Equation Formulations of Layered Media Electromagnetic Scattering Problems, arXiv:2210.02565v1 (2022), claim c002; Section IV (Second-kind integral equation formulation), eqs. (2), (4), (13), (14), (17), (18), (19), PDF pp. 3-4

import Mathlib
import Definitions.Def_Arxiv2210_02565_Basic

open Filter Topology

namespace Arxiv2210_02565

theorem muller_sie_formulation {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (ω : ℝ) (hω : 0 < ω) (ε1 μ1 k1 ε2 μ2 k2 : ℂ)
    (hk1 : k1 ^ 2 = (ω : ℂ) ^ 2 * μ1 * ε1) (hk2 : k2 ^ 2 = (ω : ℂ) ^ 2 * μ2 * ε2)
    (curlOp : W →ₗ[ℂ] W) (S1 D1 S2 D2 : V →ₗ[ℂ] W)
    (hS1 : curlOp ∘ₗ S1 = D1) (hD1 : curlOp ∘ₗ D1 = k1 ^ 2 • S1)
    (hS2 : curlOp ∘ₗ S2 = D2) (hD2 : curlOp ∘ₗ D2 = k2 ^ 2 • S2)
    (T1 K1 T2 K2 : V →ₗ[ℂ] V) (trS1 trD1 trS2 trD2 : V →ₗ[ℂ] V)
    (hjS1 : trS1 = T1) (hjD1 : ∀ φ, trD1 φ = K1 φ + (1 / 2 : ℂ) • φ)
    (hjS2 : trS2 = T2) (hjD2 : ∀ φ, trD2 φ = K2 φ - (1 / 2 : ℂ) • φ)
    (u v M J : V) :
    (curlOp (mullerE ω μ1 k1 S1 D1 u v) - (Complex.I * ω * μ1) • mullerH ω ε1 k1 S1 D1 u v = 0 ∧
      curlOp (mullerH ω ε1 k1 S1 D1 u v) + (Complex.I * ω * ε1) • mullerE ω μ1 k1 S1 D1 u v = 0 ∧
      curlOp (mullerE ω μ2 k2 S2 D2 u v) - (Complex.I * ω * μ2) • mullerH ω ε2 k2 S2 D2 u v = 0 ∧
      curlOp (mullerH ω ε2 k2 S2 D2 u v) + (Complex.I * ω * ε2) • mullerE ω μ2 k2 S2 D2 u v = 0) ∧
    ((mullerTraceE ω μ2 k2 trS2 trD2 u v - mullerTraceE ω μ1 k1 trS1 trD1 u v = M ∧
        mullerTraceH ω ε2 k2 trS2 trD2 u v - mullerTraceH ω ε1 k1 trS1 trD1 u v = J) ↔
      mullerSIE ω ε1 μ1 k1 ε2 μ2 k2 T1 K1 T2 K2 u v = (M, J)) := by sorry

end Arxiv2210_02565
