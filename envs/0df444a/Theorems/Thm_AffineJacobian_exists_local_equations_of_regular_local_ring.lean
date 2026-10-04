-- Prove2me | Theorems.Thm_AffineJacobian_exists_local_equations_of_regular_local_ring
-- name    : AffineJacobian.exists_local_equations_of_regular_local_ring
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-03T17:17:52.634999+00:00
-- url     : https://prove2.me/theorems/78858b9c-2b78-4629-ac8b-79b53b52d14a
-- title:
--   Independent local equations at a regular affine point
-- statement:
--   Let $K$ be an algebraically closed field, let $A=K[X_j\mid j\in\sigma]$ for a finite set $\sigma$, and let $I\subseteq A$ be a radical ideal. Let $a\in K^\sigma$ be a point of $V(I)$, with evaluation maximal ideal
--   $$\mathfrak m_a=\{f\in A:f(a)=0\}.$$
--   Assume that the local ring $A_{\mathfrak m_a}/IA_{\mathfrak m_a}$ is regular.
--
--   There exist $r\geq0$, polynomials $P_1,\ldots,P_r\in I$, and a polynomial $H\in A$ with $H(a)\ne0$ such that the linear map
--   $$K^\sigma\longrightarrow K^r,\qquad v\longmapsto
--   \left(\sum_{j\in\sigma}\frac{\partial P_i}{\partial X_j}(a)v_j\right)_{i=1}^r$$
--   is surjective. Moreover, on the principal open $H\ne0$ these equations define exactly the original affine zero set:
--   $$\{v:H(v)\ne0,\ P_1(v)=\cdots=P_r(v)=0\}
--   =V(I)\cap\{H\ne0\}.$$
--
--   This is the regular-point local-equation form of the Jacobian criterion in the original affine coordinates. It applies to reducible varieties and includes the case of no equations. No group structure, projective embedding, norm, or analytic chart is involved.
--
--   **Formalization Note.** The Lean reduction selects a basis of the image of the polynomial gradient map, proves the first-order Taylor identity modulo the square of the evaluation ideal, applies Nakayama after localization, and clears finitely many denominators. Its sole remaining input is [conormal injectivity for a regular quotient of a regular local ring](https://prove2.me/theorems/7f5e563c-8941-425d-90e0-9da48469dbba), a general statement with no affine or Jacobian data. The reduction actually proves equality of the localized ideals before deriving equality of zero sets on a principal open. The original formal statement is unchanged.
-- source:
--   Stacks Project, Lemma 10.140.2 (Tag 00TS), especially the converse proof which chooses f_1,...,f_c in the defining ideal and identifies the two localized quotients after a principal localization: https://stacks.math.columbia.edu/tag/00TS . The formal-Jacobian rank criterion is Lemma 10.137.15 (Tag 00TE): https://stacks.math.columbia.edu/tag/00TE . Geometric formulation: V. Platonov and A. Rapinchuk, Algebraic Groups and Number Theory (1994), section 2.4.3, Proposition 2.22, printed pp.97--98, https://uva.theopenscholar.com/files/andrei-rapinchuk/files/agnt_english.pdf . This auxiliary statement uses a finite coordinate index, a radical ideal, and the rational evaluation maximal ideal. It asks for the source proof's polynomials in the original ideal and its principal-open consequence. Algebraic closedness suffices; no characteristic-zero, irreducibility, connectedness, or positive-dimension assumption is added.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

namespace AffineJacobian

theorem exists_local_equations_of_regular_local_ring
    (K σ : Type*) [Field K] [IsAlgClosed K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (MvPolynomial.eval a))
    (hI : I.IsRadical) (hIm : I ≤ m.asIdeal)
    (hreg : IsRegularLocalRing ((Localization.AtPrime m.asIdeal) ⧸
      I.map (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal)))) :
    ∃ (r : ℕ) (P : Fin r → MvPolynomial σ K) (H : MvPolynomial σ K),
      (∀ i, P i ∈ I) ∧ MvPolynomial.eval a H ≠ 0 ∧
      Function.Surjective (fun v : σ → K => fun i : Fin r =>
        ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (P i)) * v j) ∧
      (∀ v : σ → K, MvPolynomial.eval v H ≠ 0 →
        ((∀ i, MvPolynomial.eval v (P i) = 0) ↔
          ∀ Q ∈ I, MvPolynomial.eval v Q = 0)) := by sorry

end AffineJacobian
