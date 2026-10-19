-- Prove2me | Theorems.Thm_CauchyRiemannIndex_sp2Loop_vector_homotopic_of_rhoHat_degree_zero
-- name    : CauchyRiemannIndex.sp2Loop_vector_homotopic_of_rhoHat_degree_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T16:49:19.183774+00:00
-- url     : https://prove2.me/theorems/deefa288-4ebe-45b6-9321-e0ad02ed72ee
-- title:
--   In $\mathrm{Sp}(2)$, a loop of degree zero moves $e_1$ along a null-homotopic loop in $\mathbb R^2\setminus\{0\}$
-- statement:
--   Let $\varphi:[0,1]\to\mathrm{Sp}(2,\mathbb R)=\mathrm{SL}(2,\mathbb R)$ be a continuous loop with $\varphi(0)=\varphi(1)=\mathrm{Id}$, let $\hat\rho:\mathrm{Sp}(2n,\mathbb R)\to S^1$ is the map $\hat\rho(A)=\det_{\mathbb C}C_A/|\det_{\mathbb C}C_A|$, where $C_A=\tfrac12(A-J_0AJ_0)$ is the complex linear part of $A$ (Gutt, eq. (9)), and suppose that a continuous argument $\theta$ of $\hat\rho\circ\varphi$, i.e. $\hat\rho(\varphi(t))=e^{i\theta(t)}$, satisfies $\theta(1)=\theta(0)$. Let $e_1=(1,0)\in\mathbb R^2$. Then there is a continuous map $H:[0,1]\times[0,1]\to\mathbb R^2\setminus\{0\}$ with
--   $$H(0,t)=\varphi(t)e_1,\qquad H(1,t)=e_1,\qquad H(s,0)=H(s,1)=e_1 .$$
--
--   So for $n=1$ the vanishing of the Maslov index $\deg(\hat\rho\circ\varphi)$ forces the orbit loop $t\mapsto\varphi(t)e_1$ to be null-homotopic in $\mathbb R^2\setminus\{0\}$ relative to $e_1$. It is the two-dimensional input for the statement that the Maslov index is injective on $\pi_1(\mathrm{Sp}(2n,\mathbb R))$ (Wendl, Lecture 3, §3.4).
--
--   **Formalization Note.** $\mathbb R^{2n\times2n}$ is `Mat n` (real matrices indexed by `Fin n ⊕ Fin n`, first block $q$, second block $p$) and $J_0=\begin{pmatrix}0&-\mathrm{Id}\\ \mathrm{Id}&0\end{pmatrix}$ is `Matrix.J`; `IsSymplectic A` is membership in `Matrix.symplecticGroup`. Vectors of $\mathbb R^{2n}$ are functions `Fin n ⊕ Fin n → ℝ` and $Av$ is `A *ᵥ v`. Here $n=1$, $e_1$ is `Pi.single (Sum.inl 0) 1`, $\hat\rho$ is `rhoHat`, and the argument condition is `IsArgLift (fun t => rhoHat (φ t)) θ`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 3, §3.4, p. 62 (Theorem 3.34 and the Maslov index of loops in $\mathrm{Sp}(2n)$); J. Gutt, Generalized Conley-Zehnder index, Ann. Fac. Sci. Toulouse 23 (2014), arXiv:1307.7239, §2 (the map $\hat\rho$, eq. (9))

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open Matrix

/-- For a loop `φ` in `Sp(2)` based at `Id` along which `ρ̂` has degree zero, the loop
`t ↦ φ(t) e₁` is homotopic to the constant loop `e₁` through loops in `ℝ² ∖ {0}` based at `e₁`. -/
theorem sp2Loop_vector_homotopic_of_rhoHat_degree_zero
    (φ : C(unitInterval, Mat 1)) (hs : ∀ t, IsSymplectic (φ t)) (h0 : φ 0 = 1)
    (h1 : φ 1 = 1) (θ : unitInterval → ℝ) (hθ : IsArgLift (fun t => rhoHat (φ t)) θ)
    (hθ1 : θ 1 = θ 0) :
    ∃ H : C(unitInterval × unitInterval, Fin 1 ⊕ Fin 1 → ℝ),
      (∀ t, H (0, t) = φ t *ᵥ Pi.single (Sum.inl 0) 1) ∧
      (∀ t, H (1, t) = Pi.single (Sum.inl 0) 1) ∧ (∀ p, H p ≠ 0) ∧
      (∀ s, H (s, 0) = Pi.single (Sum.inl 0) 1) ∧ ∀ s, H (s, 1) = Pi.single (Sum.inl 0) 1 := by sorry

end CauchyRiemannIndex
