-- Prove2me | Theorems.Thm_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
-- name    : Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:37.846094+00:00
-- url     : https://prove2.me/theorems/6977ce2a-53ed-5b56-af7f-b104d3f7986f
-- title:
--   A presentation with Jacobian minor nonzero at a prime
-- statement:
--   Let $R$ and $S$ be commutative rings in the same universe, with $S$ an $R$-algebra that is of finite presentation over $R$, and let $\mathfrak u \subseteq S$ be a prime ideal, with residue field $\kappa(\mathfrak u) = S_{\mathfrak u}/\mathfrak m$ (Mathlib's `Ideal.ResidueField`). Let $\iota$ be a finite index type and $w : \iota \to S$ a family of elements such that the elements $1 \otimes \mathrm{d}(w_i)$ of $\kappa(\mathfrak u) \otimes_S \Omega_{S/R}$ form a $\kappa(\mathfrak u)$-basis indexed by $\iota$; formally, a basis $b_0$ is given together with the hypothesis that $b_0(i) = 1 \otimes \mathrm{d}(w_i)$ for all $i$, where $\mathrm{d}$ is the universal derivation `KaehlerDifferential.D`. The conclusion asserts the existence of an integer $m$, elements $x : \mathrm{Fin}\, m \to S$ and polynomials $h_a \in R[T_i, X_b]$, $a \in \mathrm{Fin}\, m$, in the polynomial ring $\mathrm{MvPolynomial}(\iota \oplus \mathrm{Fin}\, m, R)$, such that: the $R$-algebra map $R[T_i, X_b] \to S$ sending $T_i \mapsto w_i$ and $X_b \mapsto x_b$ (evaluation at $\mathrm{Sum.elim}\, w\, x$) is surjective; each $h_a$ evaluates to $0$ under it; and the image of the determinant of the $m \times m$ matrix $(\partial h_a/\partial X_b)_{a,b}$ of partial derivatives with respect to the second block of variables does not lie in $\mathfrak u$.
--
--   This is the standard Jacobian-criterion selection step: if prescribed elements $w_i$ have differentials forming a basis of the cotangent fibre at $\mathfrak u$, then the finitely presented algebra $S$ admits a presentation in which the $w_i$ occur among the generators and the Jacobian minor taken with respect to the remaining variables is invertible at $\mathfrak u$. It is used by [`Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField`](thm.html#Algebra.exists_isStandardSmooth_surjective_localizationAway_basis_kaehlerDifferential_of_basis_residueField) to produce a standard smooth presentation of a localisation of $S$ away from one element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Algebra_FinitePresentation_exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct KaehlerDifferential MvPolynomial

universe u

theorem Algebra.FinitePresentation.exists_surjective_aeval_det_pderiv_not_mem_of_basis_residueField
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (u : Ideal S) [u.IsPrime]
    {ι : Type} [Finite ι] (w : ι → S)
    (b₀ : Module.Basis ι u.ResidueField (u.ResidueField ⊗[S] Ω[S⁄R]))
    (hb₀ : ∀ i, b₀ i = (1 : u.ResidueField) ⊗ₜ[S] D R S (w i)) :
    ∃ (m : ℕ) (x : Fin m → S) (h : Fin m → MvPolynomial (ι ⊕ Fin m) R),
      Function.Surjective (MvPolynomial.aeval (Sum.elim w x) : MvPolynomial (ι ⊕ Fin m) R →ₐ[R] S) ∧
      (∀ a, MvPolynomial.aeval (Sum.elim w x) (h a) = 0) ∧
      MvPolynomial.aeval (Sum.elim w x)
        (Matrix.det (Matrix.of fun a b : Fin m => MvPolynomial.pderiv (Sum.inr b) (h a))) ∉ u := by sorry
