-- Prove2me | Theorems.Thm_CauchyRiemannIndex_rhoHat_increment_eq_of_symplectic_homotopy
-- name    : CauchyRiemannIndex.rhoHat_increment_eq_of_symplectic_homotopy
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:26.135153+00:00
-- url     : https://prove2.me/theorems/054ca252-7488-4c5c-ad07-cfa237f27e9c
-- title:
--   The $\hat\rho$-increment along symplectic paths is invariant under homotopy rel end points
-- statement:
--   Let $\Phi:[0,1]\times[0,1]\to\mathrm{Sp}(2n,\mathbb R)$ be continuous with $\Phi(s,0)=\Phi(0,0)$ and $\Phi(s,1)=\Phi(0,1)$ for all $s$, and let $\hat\rho:\mathrm{Sp}(2n,\mathbb R)\to S^1$ is the map $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$, where $C_A=\tfrac12(A-J_0AJ_0)$ is the complex linear part of $A$ (Gutt, eq. (9)). If $\theta,\theta':[0,1]\to\mathbb R$ are continuous arguments of $t\mapsto\hat\rho(\Phi(0,t))$ and $t\mapsto\hat\rho(\Phi(1,t))$, i.e. $\hat\rho(\Phi(0,t))=e^{i\theta(t)}$ and $\hat\rho(\Phi(1,t))=e^{i\theta'(t)}$, then
--   $$\theta(1)-\theta(0)=\theta'(1)-\theta'(0).$$
--
--   So the total change of the argument of $\hat\rho$ along a path of symplectic matrices depends only on the homotopy class of the path relative to its end points; in particular the Maslov index $\deg(\hat\rho\circ\varphi)$ of a loop is a homotopy invariant (Gutt, §2; Wendl, Lecture 3, §3.4).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. Vectors of $\mathbb R^{2n}$ are functions `Fin n ⊕ Fin n → ℝ` and $Av$ is `A *ᵥ v`. $\hat\rho$ is `rhoHat` and the argument conditions are `IsArgLift (fun t => rhoHat (Φ (0, t))) θ` and `IsArgLift (fun t => rhoHat (Φ (1, t))) θ'` from the setting definitions.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- The total change of a continuous argument of `ρ̂` along a path of symplectic matrices is
unchanged under homotopies of symplectic paths with fixed end points. -/
theorem rhoHat_increment_eq_of_symplectic_homotopy {n : ℕ}
    (Φ : C(unitInterval × unitInterval, Mat n)) (hs : ∀ p, IsSymplectic (Φ p))
    (h0 : ∀ s, Φ (s, 0) = Φ (0, 0)) (h1 : ∀ s, Φ (s, 1) = Φ (0, 1)) (θ θ' : unitInterval → ℝ)
    (hθ : IsArgLift (fun t => rhoHat (Φ (0, t))) θ)
    (hθ' : IsArgLift (fun t => rhoHat (Φ (1, t))) θ') :
    θ 1 - θ 0 = θ' 1 - θ' 0 := by sorry

end CauchyRiemannIndex
