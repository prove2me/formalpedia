-- Prove2me | Theorems.Thm_FiniteEnergyPlane_linReebFlow_unitaryFrame_eq
-- name    : FiniteEnergyPlane.linReebFlow_unitaryFrame_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-02T17:41:51.437582+00:00
-- url     : https://prove2.me/theorems/c389a7c7-0338-4601-b869-d628f63924a0
-- title:
--   In a unitary frame, the linearized Reeb flow is the fundamental solution of the asymptotic operator's matrix
-- statement:
--   Let $H:\mathbb{R}^{2n+2}\to\mathbb{R}$ have a strictly star-shaped level $S=H^{-1}(1)$ and let $Q=(x,T)$ be a periodic Reeb orbit on $S$. Let $Z$ be a unitary frame of $\xi$ along $Q$ (a smooth $1$-periodic family of linear isomorphisms $Z(t):\mathbb{R}^{2n}\to\xi_{x(Tt)}$ with $JZ=ZJ_0$ and $\omega_0(Za,Zb)=\langle J_0a,b\rangle$), and let $S_\infty$ be a loop of $2n\times 2n$ matrices such that the asymptotic operator of $Q$ takes the form
--   $$A_Q(Z\eta)=Z\,(-J_0\eta'-S_\infty\eta)\qquad\text{for all smooth $1$-periodic }\eta:\mathbb{R}\to\mathbb{R}^{2n}.$$
--   Let $\Psi$ be the fundamental solution of $S_\infty$ ($\Psi(0)=I$, $\Psi'=J_0S_\infty\Psi$) and $\Phi$ the linearized Reeb flow along $Q$ ($\Phi(0)=\mathrm{id}$, $\Phi'(\tau)=DR(x(\tau))\Phi(\tau)$). Then
--   $$\Phi(Tt)\,Z(0)a=Z(t)\,\Psi(t)a\qquad\text{for all }t\in\mathbb{R},\ a\in\mathbb{R}^{2n}.$$
--
--   So in such a frame the linearized Reeb flow on $\xi$, run at speed $T$, is the fundamental solution $\Psi$ of the matrix form of the asymptotic operator. This identifies the Conley–Zehnder data of $Q$ (from $\Phi$) with the matrix data $\Psi$ used for the operator $-J_0\partial_t-S_\infty$.
--
--   **Formalization Note** The setting is `FiniteEnergyPlane` on `V n` with `CauchyRiemannIndex.Vec n` $=\mathbb{R}^{2n}$ and `CauchyRiemannIndex.Mat n`. The frame is `IsUnitaryXiFrame J Q Z`, the asymptotic operator is `asympOp J Q`, $\Phi$ is `IsLinReebFlow Q Φ` and $\Psi$ is `CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ`; matrices act through `Matrix.toEuclideanLin`. No compatibility hypothesis on `J` is assumed beyond the frame conditions; no symmetry or continuity of `Sinf` is assumed.
-- source:
--   U. Hryniewicz, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Definition 2.5 and Remark 2.6; H. Hofer, K. Wysocki, E. Zehnder, Ann. Inst. H. Poincare Anal. Non Lineaire 13 (1996), Section 3

import Definitions.Def_FiniteEnergyPlane_Asymptotics

open FiniteEnergyPlane
open scoped ContDiff

/-- Let `Z` be a unitary frame of `ξ` along a periodic Reeb orbit `Q = (x, T)` in which the
asymptotic operator takes the form `A_Q(Z η) = Z(-J₀ η' - S∞ η)` for smooth `1`-periodic `η`. Let
`Ψ` be the fundamental solution of `S∞` and `Φ` the linearized Reeb flow along `Q`. Then
`Φ(T t)(Z(0) a) = Z(t)(Ψ(t) a)` for all `t` and `a`. -/
theorem FiniteEnergyPlane.linReebFlow_unitaryFrame_eq {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n) (Q : ReebOrbit H)
    (Z : ℝ → CauchyRiemannIndex.Vec n →L[ℝ] V n) (hZ : IsUnitaryXiFrame J Q Z)
    (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec n, ContDiff ℝ ∞ η → Function.Periodic η 1 →
      ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
        Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (deriv η t)) -
          Matrix.toEuclideanLin (Sinf t) (η t)))
    (Ψ : ℝ → CauchyRiemannIndex.Mat n) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ)
    (Φ : ℝ → V n →L[ℝ] V n) (hΦ : IsLinReebFlow Q Φ) :
    ∀ (t : ℝ) (a : CauchyRiemannIndex.Vec n),
      Φ (Q.T * t) (Z 0 a) = Z t (Matrix.toEuclideanLin (Ψ t) a) := by sorry
