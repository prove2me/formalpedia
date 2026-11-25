-- Prove2me | Theorems.Thm_Arxiv2608_05214_liouville_schrodinger
-- name    : Arxiv2608_05214.liouville_schrodinger
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:15:31.580856+00:00
-- url     : https://prove2.me/theorems/c3e2d790-5464-52cc-a2d5-be1626f2d0a5
-- title:
--   Eqs. (17)-(18): the impedance scaling gives the 1D acoustic Schrödinger equation
-- statement:
--   Let $\eta:\mathbb R\to(0,\infty)$ be twice continuously differentiable, the square root of the impedance as a function of traveltime, and let $\psi(\tau,t)$ be twice continuously differentiable in $\tau$. Put $u=\psi/\eta$ and $q=\eta''/\eta$. Then for all $\tau,t$
--
--   $$\eta^2\,\partial_t^2u-\partial_\tau\big(\eta^2\,\partial_\tau u\big)=\eta\,\Big(\partial_t^2\psi-\partial_\tau^2\psi+q(\tau)\,\psi\Big).$$
--
--   Since $\eta>0$, $u$ solves Webster's horn equation (15) with impedance $\eta^2$ exactly when $\psi$ solves the 1D acoustic Schrödinger equation (17). Moreover the potential vanishes wherever the impedance is locally constant: if $\eta$ is constant on a neighbourhood of $\tau$, then $q(\tau)=0$.
--
--   **Formalization Note** The paper's remarks that $q$ is frequency independent (it is a function of $\tau$ alone by construction) and that this is the setting of classical Gelfand–Levitan–Marchenko theory are commentary and are not stated.
-- source:
--   H. A. Oyekan, Marchenko Theory, Algorithms, and Applications: A Review, arXiv:2608.05214v1 (2026), claim c021; Section III-B (Step 1), eqs. (16)-(18) and the following paragraphs, PDF p. 5

import Mathlib
import Definitions.Def_Arxiv2608_05214_Basic

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Arxiv2608_05214

theorem liouville_schrodinger (η : ℝ → ℝ) (ψ : ℝ → ℝ → ℝ)
    (hηpos : ∀ τ, 0 < η τ) (hη : ContDiff ℝ 2 η) (hψ : ∀ t, ContDiff ℝ 2 (fun τ => ψ τ t)) :
    (∀ τ t : ℝ, hornEqLHS (fun τ => η τ ^ 2) (fun τ t => ψ τ t / η τ) τ t =
        η τ * schrodingerLHS (scatteringPotential η) ψ τ t) ∧
    (∀ τ : ℝ, (∀ᶠ σ in 𝓝 τ, η σ = η τ) → scatteringPotential η τ = 0) := by sorry

end Arxiv2608_05214
