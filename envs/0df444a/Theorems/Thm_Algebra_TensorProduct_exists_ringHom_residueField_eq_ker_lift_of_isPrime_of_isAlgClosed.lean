-- Prove2me | Theorems.Thm_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed
-- name    : Algebra.TensorProduct.exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/13ac8fa7-a1ed-5b76-ac96-85014b5928e2
-- title:
--   Primes over both closed points are kernels of κ(A)-characters
-- statement:
--   Let $A_0$ and $A$ be local rings with $A$ an $A_0$-algebra whose structure map $A_0 \to A$ is a local homomorphism, and assume the residue field $\kappa(A)$ of $A$ is algebraically closed. Let $B_0$ be an $A_0$-algebra of finite type, and let $\mathfrak m_0 \subseteq B_0$ be a maximal ideal such that the image in $B_0$ of every element of the maximal ideal of $A_0$ lies in $\mathfrak m_0$. Let $P$ be a prime ideal of $A \otimes_{A_0} B_0$ such that $1 \otimes b \in P$ for all $b \in \mathfrak m_0$ and $a \otimes 1 \in P$ for all $a$ in the maximal ideal of $A$. The assertion is that there exists a ring homomorphism $\chi \colon B_0 \to \kappa(A)$ compatible with the two structure maps, in the sense that $\chi(\text{image of } a) = \overline{\text{image of } a}$ in $\kappa(A)$ for every $a \in A_0$, such that $P$ is exactly the kernel of the ring homomorphism $A \otimes_{A_0} B_0 \to \kappa(A)$ obtained by tensor-product lifting of the residue map $A \to \kappa(A)$ and of $\chi$, i.e. of $a \otimes b \mapsto \bar a\,\chi(b)$. In particular such a $P$ is maximal with residue field $\kappa(A)$.
--
--   This is the description, in the style of the computation of the points of a fibre product with values in an algebraically closed field, of those primes of a base-changed finite-type algebra that lie over the closed point of $\operatorname{Spec} A$ and over the given maximal ideal $\mathfrak m_0$: they are the kernels of $\kappa(A)$-valued characters, Zariski's lemma providing the rationality of the residue field. It is used in the analysis of the completed local rings of base-changed Drinfeld charts on modular curves, where it both identifies the chosen point with a kernel and supplies the character $\chi$ entering the subsequent description of the stalk.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_TensorProduct_exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing TensorProduct

theorem Algebra.TensorProduct.exists_ringHom_residueField_eq_ker_lift_of_isPrime_of_isAlgClosed
    (A₀ A : Type) [CommRing A₀] [IsLocalRing A₀] [CommRing A] [IsLocalRing A] [Algebra A₀ A]
    [IsLocalHom (algebraMap A₀ A)] [IsAlgClosed (ResidueField A)]
    (B₀ : Type) [CommRing B₀] [Algebra A₀ B₀] [Algebra.FiniteType A₀ B₀]
    (𝔪₀ : Ideal B₀) [𝔪₀.IsMaximal] (h𝔪₀ : ∀ a ∈ maximalIdeal A₀, algebraMap A₀ B₀ a ∈ 𝔪₀)
    (P : Ideal (A ⊗[A₀] B₀)) [P.IsPrime]
    (hP₀ : ∀ b ∈ 𝔪₀, (1 : A) ⊗ₜ[A₀] b ∈ P)
    (hPA : ∀ a ∈ maximalIdeal A, a ⊗ₜ[A₀] (1 : B₀) ∈ P) :
    ∃ (χ : B₀ →+* ResidueField A)
      (hχA₀ : ∀ a : A₀, χ (algebraMap A₀ B₀ a) = IsLocalRing.residue A (algebraMap A₀ A a)),
      let ev : A ⊗[A₀] B₀ →+* ResidueField A :=
        (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom A₀ A (ResidueField A))
          ({ toRingHom := χ, commutes' := fun a => by
              rw [IsScalarTower.algebraMap_apply A₀ A (ResidueField A)]; exact hχA₀ a } : B₀ →ₐ[A₀] ResidueField A)
          (fun _ _ => Commute.all _ _)).toRingHom
      P = RingHom.ker ev := by sorry
