-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_normalFrame_of_isFastPlane
-- name    : FiniteEnergyPlane.exists_normalFrame_of_isFastPlane
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T19:23:58.563111+00:00
-- url     : https://prove2.me/theorems/80d14cc7-9588-4d13-8a06-a111ca590e5d
-- title:
--   A unitary normal frame along a fast finite-energy plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$ be a strictly star-shaped level with contact structure $\xi$, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, and $\tilde J$ the induced cylindrical almost complex structure on $\mathbb R^4\setminus\{0\}$. Write $a(y)$ and $\mathrm{proj}(y)\in S$ for the symplectization coordinates of $y\ne0$ ($y=e^{2a}\,\mathrm{proj}(y)$). Let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be a fast finite-energy $\tilde J$-holomorphic plane (Hryniewicz, Definition 2.14) with a nondegenerate end at the periodic Reeb orbit $P=(x,T)$.
--
--   Then there are $d,c\in\mathbb R$, $b>0$, a smooth family of real-linear maps $N(z):\mathbb C\to\mathbb R^4$ ($z\in\mathbb C$), and a unitary frame $M(t):\mathbb R^2\to\xi_{x(Tt+c)}$ of $\xi$ along the shifted orbit $P'=(x(\cdot+c),T)$ such that, in the coordinates $z=e^{2\pi(s+it)}$:
--   1. $a(u)-Ts-d$ and $\mathrm{proj}(u)-x(Tt+c)$ decay like $e^{-bs}$ in $C^\infty$, uniformly in $t$;
--   2. $N(z)(i\nu)=\tilde J(u(z))\,N(z)\nu$ for all $z,\nu$;
--   3. $(\Delta,\nu)\mapsto Du(z)\Delta+N(z)\nu$ is injective on $\mathbb C\times\mathbb C$ for every $z$;
--   4. $u(0)\in N(0)1+Du(0)\mathbb C$;
--   5. $M$ has winding one: a continuous $1$-periodic nowhere-vanishing loop $\zeta$ in $\mathbb R^2\cong\mathbb C$ has winding number $k$ if and only if the loop $t\mapsto M(t)\zeta(t)$ in $\xi$ has winding number $k+1$ in the global frame of $\xi$;
--   6. for every $\nu\in\mathbb C$, $e^{-2(Ts+d)}N(e^{2\pi(s+it)})\nu-M(t)\nu$ decays like $e^{-bs}$ in $C^\infty$, uniformly in $t$.
--
--   The frame $N$ is the normal direction of a tubular neighbourhood of the plane adapted to $\tilde J$, used to build a standard tube around a fast plane.
--
--   Formalization Note: `V 1` is $\mathbb R^4$; $N(z)$ is `N z : ℂ →L[ℝ] V 1`; $M(t)$ is `M t : Vec 1 →L[ℝ] V 1` with `IsUnitaryXiFrame J P' M`, and $M(t)\nu$ means `M t (cToVec ν)`; windings are `HasXiLoopWind` / `HasLoopWind`; decay is `ExpDecayCInfty` along `endA`, `endW` with `cylInf`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), proof of Lemma 6.10

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A unitary normal frame along a fast plane. Let `u` be a fast finite-energy plane with a
nondegenerate end at `P`. Then there are `d, c`, `b > 0`, the shifted orbit `P'`
(`x'(τ) = x(τ + c)`, same period), a smooth family `N z : ℂ →L[ℝ] V 1` and a unitary frame `M` of
`ξ` along `P'` such that: in the coordinates `z = e^{2π(s+it)}`, `aCoord (u) - T s - d` and
`proj (u) - x'(T t)` decay like `e^{-bs}` in `C^∞`; each `N z` is complex linear for `J̃(u z)`;
`(Δ, ν) ↦ Du(z) Δ + N z ν` is injective for every `z`; `u 0 ∈ N 0 1 + Du(0) ℂ`; `M` has winding
one (a nowhere-vanishing loop `ζ` has winding `k` iff `M ζ` has winding `k + 1` in the global
frame); and `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decays like `e^{-bs}` in `C^∞` for every
`ν`. -/
theorem exists_normalFrame_of_isFastPlane (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1)
    (hu : IsFastPlane H J u) (huP : IsNondegenerateEnd H u cylInf P 1) :
    ∃ (d c b : ℝ) (P' : ReebOrbit H) (N : ℂ → ℂ →L[ℝ] V 1)
      (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1),
      0 < b ∧ P'.T = P.T ∧ (∀ τ : ℝ, P'.x τ = P.x (τ + c)) ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b ∧
      ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P'.x (P.T * p.2)) b ∧
      ContDiff ℝ ∞ N ∧
      (∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν)) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0) ∧
      (∃ τ : ℂ, fderiv ℝ u 0 τ + N 0 1 = u 0) ∧
      IsUnitaryXiFrame J P' M ∧
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P' (fun t => M t (ζ t)) (k + 1) ↔
            HasLoopWind (fun t => vecToC (ζ t)) k)) ∧
      ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
        Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b := by
  sorry

end FiniteEnergyPlane
