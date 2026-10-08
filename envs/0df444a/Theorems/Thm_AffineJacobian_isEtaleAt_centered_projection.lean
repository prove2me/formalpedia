-- Prove2me | Theorems.Thm_AffineJacobian_isEtaleAt_centered_projection
-- name    : AffineJacobian.isEtaleAt_centered_projection
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T14:24:28.675133+00:00
-- url     : https://prove2.me/theorems/32c076c8-0e38-4812-b2d0-fb2108d5f699
-- title:
--   The Jacobian criterion for a centered étale projection
-- statement:
--   Let $K$ be an arbitrary field, let $\sigma$ be a finite set, and let $r,d\geq0$. Put
--   $$A=K[X_j\mid j\in\sigma],\qquad J=(F_1,\ldots,F_r),\qquad C=A/J,$$
--   where $F_1,\ldots,F_r\in A$ vanish at $a\in K^\sigma$. Let $c_{ij}\in K$ be a $d\times|\sigma|$ matrix and assume that
--   $$K^\sigma\longrightarrow K^r\times K^d,\qquad v\longmapsto (JF(a)v,cv)$$
--   is a linear isomorphism. Define $B=K[T_1,\ldots,T_d]$ and the $K$-algebra map
--   $$B\longrightarrow C,\qquad T_i\longmapsto \overline{t_i},\qquad t_i=\sum_{j\in\sigma}c_{ij}(X_j-a_j).$$
--   Let $\mathfrak q$ be the prime of $C$ corresponding to the rational point $a$; equivalently, its inverse image under $A\to C$ is $\ker(\operatorname{ev}_a)$. Then this map $B\to C$ is étale at $\mathfrak q$.
--
--   The assertion is local at the chosen point: it does not require $J$ to be prime or radical, or the projection to be étale everywhere. There is no assumption of characteristic zero, perfection, or algebraic closure. The cases of empty coordinate sets, $r=0$, and $d=0$ are included.
--
--   **Formalization Note.** Mathlib's Algebra.IsEtaleAt B q asserts formal étaleness of the localized algebra at the prime. The complete proof constructs the graph presentation over $K[T]$, proves its relation ideal equals the kernel, identifies its Jacobian with the augmented derivative matrix, and localizes at its nonvanishing determinant. The resulting presentation is standard smooth of relative dimension zero, hence étale. The standalone Lean implementation imports only Mathlib; all original hypotheses and the formal statement are unchanged, including the arbitrary-field and empty-coordinate cases.
-- source:
--   Stacks Project, Definition 10.137.5 (Tag 00T6), https://stacks.math.columbia.edu/tag/00T6 ; Lemma 10.137.6(1),(2),(4) (Tag 00T7), https://stacks.math.columbia.edu/tag/00T7 ; Definition 10.143.1 and the opening characterization of etale maps as smooth maps of relative dimension zero (Tag 00U0), https://stacks.math.columbia.edu/tag/00U0 . Explicit specialization: present C over B by the equations F_i(X) and T_i-t_i(X). The augmented linear isomorphism forces the number of these equations to equal the number of X variables. Its Jacobian determinant is nonzero at a (the bottom rows differ by a sign). Inverting that determinant gives a standard-smooth presentation of relative dimension zero, hence an etale neighborhood. The construction of this presentation and its Jacobian identification is the Open formalization obligation; this is not claimed as a verbatim numbered source statement.

import Mathlib

set_option autoImplicit false
open scoped BigOperators

namespace AffineJacobian

theorem isEtaleAt_centered_projection
    (K σ : Type*) [Field K] [Fintype σ]
    (r d : ℕ) (F : Fin r → MvPolynomial σ K) (a : σ → K)
    (hF : ∀ i, MvPolynomial.eval a (F i) = 0)
    (c : Fin d → σ → K)
    (L : (σ → K) ≃ₗ[K] ((Fin r → K) × (Fin d → K)))
    (hL : ∀ v, L v =
      ((fun i => ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (F i)) * v j),
       (fun i => ∑ j, c i j * v j)))
    (q : Ideal ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F))) [q.IsPrime]
    (hq : q.comap (Ideal.Quotient.mk (Ideal.span (Set.range F))) =
      RingHom.ker (MvPolynomial.eval a)) :
    letI : Algebra (MvPolynomial (Fin d) K)
        ((MvPolynomial σ K) ⧸ Ideal.span (Set.range F)) :=
      ((Ideal.Quotient.mk (Ideal.span (Set.range F))).comp
        (MvPolynomial.aeval (fun i => ∑ j,
          MvPolynomial.C (c i j) * (MvPolynomial.X j - MvPolynomial.C (a j)))).toRingHom).toAlgebra
    Algebra.IsEtaleAt (MvPolynomial (Fin d) K) q := by sorry

end AffineJacobian
