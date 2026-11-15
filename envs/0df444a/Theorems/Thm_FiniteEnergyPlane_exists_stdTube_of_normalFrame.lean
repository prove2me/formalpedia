-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_stdTube_of_normalFrame
-- name    : FiniteEnergyPlane.exists_stdTube_of_normalFrame
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-14T19:23:59.19299+00:00
-- url     : https://prove2.me/theorems/cf06b670-da02-4057-ad40-7b765987c113
-- title:
--   A standard tube from a complex normal frame along a holomorphic plane
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^4$ be a strictly star-shaped level, $J$ a $d\lambda_0$-compatible complex structure on $\xi$, $\tilde J$ the induced cylindrical almost complex structure on $\mathbb R^4\setminus\{0\}$, and $P=(x,T)$ a periodic Reeb orbit. Write $a(y)$, $\mathrm{proj}(y)$ for the symplectization coordinates ($y=e^{2a}\,\mathrm{proj}(y)$) and use $z=e^{2\pi(s+it)}$ near $\infty$.
--
--   Let $u:\mathbb C\to\mathbb R^4\setminus\{0\}$ be smooth and $\tilde J$-holomorphic, with $a(u)-Ts-d$ and $\mathrm{proj}(u)-x(Tt)$ decaying like $e^{-bs}$ in $C^\infty$ ($b>0$). Let $N(z):\mathbb C\to\mathbb R^4$ be a smooth family of real-linear maps with $N(z)(i\nu)=\tilde J(u(z))N(z)\nu$ and $(\Delta,\nu)\mapsto Du(z)\Delta+N(z)\nu$ injective for every $z$, and let $M$ be a unitary frame of $\xi$ along $P$ such that $e^{-2(Ts+d)}N(e^{2\pi(s+it)})\nu-M(t)\nu$ decays like $e^{-bs}$ in $C^\infty$ for every $\nu$.
--
--   Then, for $\Phi(z,w)=u(z)+N(z)w$, there are $\rho,b'>0$ and a standard tube structure $(\bar J,J_\infty,S_\infty)$ of width $\rho$ and rate $b'$ (`IsStdTubeStructure`) such that:
--   1. $S_\infty$ is smooth and $A_P(M\eta)=M(-J_0\eta'-S_\infty\eta)$ for every smooth $1$-periodic $\eta$, where $A_P$ is the asymptotic operator of $P$;
--   2. $D\Phi(z,0)(\Delta,\nu)=Du(z)\Delta+N(z)\nu$;
--   3. on $\mathbb C\times B_\rho(0)$: $\Phi\neq0$, $D\Phi$ is injective, and $D\Phi\circ\bar J=\tilde J(\Phi)\circ D\Phi$;
--   4. there are smooth $1$-periodic $\alpha(t,w)$, $X(t,w)$ on $\mathbb R\times B_\rho(0)$ with $\alpha(t,0)=0$, $X(t,0)=x(Tt)$, such that $a(\Phi(e^{2\pi(s+it)},w))-Ts-d-\alpha(t,w)$ and $\mathrm{proj}(\Phi(e^{2\pi(s+it)},w))-X(t,w)$ decay like $e^{-b's}$ in $C^\infty$, uniformly in $t$ and $w\in B_\rho(0)$.
--
--   This produces, from a complex normal frame along a holomorphic plane with cylindrical asymptotics, the coordinates in which the plane is $\{w=0\}$ and the almost complex structure is standard along it.
--
--   Formalization Note: `V 1` is $\mathbb R^4$; $N(z)$ is `N z : ℂ →L[ℝ] V 1`, $M(t)\nu$ is `M t (cToVec ν)` with `IsUnitaryXiFrame J P M`; $\Phi$ is written out as `fun q => u q.1 + N q.1 q.2`; decay is `ExpDecayCInfty` / `ExpDecayCInftyTube`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), proof of Lemma 6.10

import Definitions.Def_FiniteEnergyPlane_TubeFamily
import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A standard tube from a complex normal frame. Let `u : ℂ → V 1 \ {0}` be smooth and
`J̃`-holomorphic, with `aCoord (u) - T s - d` and `proj (u) - x(T t)` decaying like `e^{-bs}` in
`C^∞` in the coordinates `z = e^{2π(s+it)}`. Let `N z : ℂ →L[ℝ] V 1` be smooth, complex linear for
`J̃(u z)`, with `(Δ, ν) ↦ Du(z) Δ + N z ν` injective, and let `M` be a unitary frame of `ξ` along
`P` such that `e^{-2(Ts+d)} N(e^{2π(s+it)}) ν - M(t) ν` decays like `e^{-bs}` in `C^∞`. Then for
`Φ(z, w) = u z + N z w` there are `ρ, b' > 0` and a standard tube structure `(Jbar, Jinf, Sinf)`
of width `ρ` and rate `b'` such that: `Sinf` is smooth and `A_P (M η) = M (-J₀ η' - Sinf η)` for
smooth `1`-periodic `η`; `DΦ(z, 0)(Δ, ν) = Du(z) Δ + N z ν`; on `ℂ × ball 0 ρ`, `Φ ≠ 0`, `DΦ` is
injective and `DΦ ∘ Jbar = J̃(Φ) ∘ DΦ`; and there are smooth `1`-periodic `α`, `X` with
`α(t, 0) = 0`, `X(t, 0) = x(T t)` such that `aCoord (Φ) - T s - d - α(t, w)` and
`proj (Φ) - X(t, w)` decay exponentially in `C^∞`, uniformly in `w`. -/
theorem exists_stdTube_of_normalFrame (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (u : ℂ → V 1) (hu : ContDiff ℝ ∞ u) (hu0 : ∀ z, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) Set.univ u) (d b : ℝ) (hb : 0 < b)
    (ha : ExpDecayCInfty (fun p : ℝ × ℝ => endA H u cylInf p - P.T * p.1 - d) b)
    (hw : ExpDecayCInfty (fun p : ℝ × ℝ => endW H u cylInf p - P.x (P.T * p.2)) b)
    (N : ℂ → ℂ →L[ℝ] V 1) (hN : ContDiff ℝ ∞ N)
    (hNJ : ∀ (z ν : ℂ), N z (Complex.I * ν) = Jtilde H J (u z) (N z ν))
    (hNinj : ∀ (z Δ ν : ℂ), fderiv ℝ u z Δ + N z ν = 0 → Δ = 0 ∧ ν = 0)
    (M : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hM : IsUnitaryXiFrame J P M)
    (hNM : ∀ ν : ℂ, ExpDecayCInfty (fun p : ℝ × ℝ =>
      Real.exp (-(2 * (P.T * p.1 + d))) • N (cylInf p.1 p.2) ν - M p.2 (cToVec ν)) b) :
    ∃ ρ > 0, ∃ b' > 0, ∃ (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
      (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1),
      IsStdTubeStructure ρ b' Jbar Jinf Sinf ∧
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) ∧
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J P (fun t => M t (η t)) t =
          M t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) ∧
      (∀ (z Δ ν : ℂ), fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) (z, 0) (Δ, ν) =
        fderiv ℝ u z Δ + N z ν) ∧
      (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ, u p.1 + N p.1 p.2 ≠ 0 ∧
        Function.Injective (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p) ∧
        (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p).comp (Jbar p) =
          (Jtilde H J (u p.1 + N p.1 p.2)).comp
            (fderiv ℝ (fun q : ℂ × ℂ => u q.1 + N q.1 q.2) p)) ∧
      (∃ (α : ℝ × ℂ → ℝ) (X : ℝ × ℂ → V 1),
        ContDiffOn ℝ ∞ α (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        ContDiffOn ℝ ∞ X (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
        (∀ (t : ℝ) (w : ℂ), α (t + 1, w) = α (t, w) ∧ X (t + 1, w) = X (t, w)) ∧
        (∀ t : ℝ, α (t, 0) = 0 ∧ X (t, 0) = P.x (P.T * t)) ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          aCoord H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - P.T * q.1 - d -
            α (q.2.1, q.2.2)) ρ b' ∧
        ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ =>
          proj H (u (cylInf q.1 q.2.1) + N (cylInf q.1 q.2.1) q.2.2) - X (q.2.1, q.2.2)) ρ b') := by
  sorry

end FiniteEnergyPlane
