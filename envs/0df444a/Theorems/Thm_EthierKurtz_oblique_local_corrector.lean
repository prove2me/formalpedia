-- Prove2me | Theorems.Thm_EthierKurtz_oblique_local_corrector
-- name    : EthierKurtz.oblique_local_corrector
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-25T05:14:58.319618+00:00
-- url     : https://prove2.me/theorems/6c9673e5-94d5-4a3f-b28d-9002402593eb
-- title:
--   Local oblique corrector at a boundary point of a C^{2,mu} domain
-- statement:
--   Let $\Omega\subset\mathbb{R}^{n+1}$ be open, $0<\mu\le1$, let $c$ be a vector field on $\partial\Omega$ whose components are $C^{1,\mu}$ in the boundary graph charts, $\nu$ the outward unit normal, and suppose $c\cdot\nu\ge\varepsilon>0$ on $\partial\Omega$. Assume the flat lifting lemma (hypothesis `hlift`: every compactly supported $C^{1,\mu}$ datum $q$ on $\mathbb{R}^n$ has a small $C^1$ lift $W$ on $\mathbb{R}^n\times\mathbb{R}$ with $W(z,0)=0$, $DW(z,0)=q(z)\,dt$, $C^{2,\mu}$ on $\{t>0\}$). Then every $x_0\in\partial\Omega$ has a radius $\rho>0$ such that for all smooth $F,\xi$ with $\operatorname{supp}\xi\subset B(x_0,\rho)$ and every $\delta>0$ there is a compactly supported $C^1$ function $V$ with $|V|\le\delta$, $V\in C^{2,\mu}(\Omega)$ and
--   $$DV(x)\,c(x) = -\xi(x)\,DF(x)\,c(x)\qquad (x\in\partial\Omega).$$
--
--   Role: in the parent's density step, $F$ is a smooth approximation of $f$ and the correctors $V$ from finitely many boundary balls (with a partition of unity $\xi_k$) cancel the oblique derivative $c\cdot DF$ on $\partial\Omega$, giving functions in the domain of the reflected generator.
--
--   **Formalization Note**: the flat lift is taken as a hypothesis (it is the sibling child `EthierKurtz.oblique_flat_lift`), so this statement isolates the chart geometry; $C^{1,\mu}$ of $c$ is the platform's `BoundaryCOnceHolder`.
-- source:
--   D. Gilbarg and N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer, 2001, Section 6.7 (oblique derivative problem: local flattening and lifting of boundary data); used in Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, https://doi.org/10.1002/9780470316658, Chapter 8, Section 1

import Mathlib
import Definitions.Def_EthierKurtz_BoundaryCOnceHolder
import Definitions.Def_EthierKurtz_IsOutwardUnitNormal
import Definitions.Def_EthierKurtz_CTwiceHolder

open scoped ContDiff

namespace EthierKurtz

theorem oblique_local_corrector (n : ℕ)
    (Ω : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hopen : IsOpen Ω) (μ : ℝ) (hμ : 0 < μ ∧ μ ≤ 1)
    (c normal : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hc : ∀ i, BoundaryCOnceHolder Ω μ (fun x => c x i))
    (hnormal : ∀ x ∈ frontier Ω, IsOutwardUnitNormal Ω x (normal x))
    (hoblique : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ frontier Ω, ε ≤ ∑ i, c x i * normal x i)
    (hlift : ∀ q : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 q → HasCompactSupport q →
      (∃ M : ℝ, ∀ x y, ‖fderiv ℝ q x - fderiv ℝ q y‖ ≤ M * ‖x - y‖ ^ μ) →
      ∀ δ : ℝ, 0 < δ →
      ∃ W : EuclideanSpace ℝ (Fin n) × ℝ → ℝ,
        ContDiff ℝ 1 W ∧ HasCompactSupport W ∧
        ContDiffOn ℝ 2 W {p | 0 < p.2} ∧
        (∀ z, W (z, 0) = 0) ∧
        (∀ z, fderiv ℝ W (z, 0) = q z • ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n)) ℝ) ∧
        (∀ p, |W p| ≤ δ) ∧
        ∃ K : ℝ, ∀ p p' : EuclideanSpace ℝ (Fin n) × ℝ, 0 < p.2 → 0 < p'.2 →
          ‖fderiv ℝ (fderiv ℝ W) p - fderiv ℝ (fderiv ℝ W) p'‖ ≤ K * ‖p - p'‖ ^ μ) :
    ∀ x₀ ∈ frontier Ω, ∃ ρ : ℝ, 0 < ρ ∧
      ∀ F ξ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ξ → tsupport ξ ⊆ Metric.ball x₀ ρ →
        ∀ δ : ℝ, 0 < δ →
          ∃ V : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
            ContDiff ℝ 1 V ∧ HasCompactSupport V ∧ (∀ x, |V x| ≤ δ) ∧
            CTwiceHolder Ω μ V ∧
            ∀ x ∈ frontier Ω, fderiv ℝ V x (c x) = -(ξ x * fderiv ℝ F x (c x)) := by sorry

end EthierKurtz
