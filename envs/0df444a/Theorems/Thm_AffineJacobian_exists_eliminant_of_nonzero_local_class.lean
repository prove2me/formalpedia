-- Prove2me | Theorems.Thm_AffineJacobian_exists_eliminant_of_nonzero_local_class
-- name    : AffineJacobian.exists_eliminant_of_nonzero_local_class
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-04T13:06:52.373266+00:00
-- url     : https://prove2.me/theorems/eb5e1a51-f166-4126-a10e-047703c0baa0
-- title:
--   A nonzero eliminant for a hypersurface in nonsingular local coordinates
-- statement:
--   Let $K$ be a field, let $\sigma$ be a finite set, and put $A=K[X_j\mid j\in\sigma]$. Fix nonnegative integers $r,d$, polynomials $F_1,\ldots,F_r\in A$, and a point $a\in K^\sigma$ with $F_i(a)=0$ for every $i$. Write $J=(F_1,\ldots,F_r)$ and $\mathfrak m_a=\ker(\operatorname{ev}_a)$.
--
--   Let $C=(c_{ij})$ be a $d\times|\sigma|$ matrix. Assume that the augmented Jacobian is a linear isomorphism:
--   $$K^\sigma\longrightarrow K^r\times K^d,\qquad v\longmapsto (JF(a)v,Cv).$$
--   Define the centered linear coordinate polynomials
--   $$t_i(X)=\sum_{j\in\sigma}c_{ij}(X_j-a_j),\qquad 1\le i\le d.$$
--   For every $P\in A$ whose class in $A_{\mathfrak m_a}/JA_{\mathfrak m_a}$ is nonzero, there exist $Q\in K[T_1,\ldots,T_d]$ and $H\in A$ such that
--   $$Q\ne0,\qquad H(a)\ne0,\qquad H(X)Q(t_1(X),\ldots,t_d(X))\in J+(P).$$
--
--   This gives a nonzero polynomial constraint on the projection of the hypersurface $P=0$ in the nonsingular local component of $F=0$, after restriction to the principal neighborhood $D(H)$ of $a$. The statement is purely algebraic: it makes no assumption on a norm, completeness, characteristic, or algebraic closure. The cases $r=0$, $d=0$, and $\sigma=\varnothing$ are included. The zero scheme of $J$ need not be irreducible or nonsingular away from $a$.
--
--   **Formalization Note.** The checked reduction proves the generic-fiber algebraicity, regular-local-domain, nonzero coefficient, and localization-denominator steps. Its sole remaining input is the [Jacobian criterion for the centered étale projection](https://prove2.me/theorems/32c076c8-0e38-4812-b2d0-fb2108d5f699). This remaining geometric statement is independent of $P$ and of the requested certificate. All hypotheses and the original formal statement are unchanged.
-- source:
--   Stacks Project, Definition 10.137.5 (Tag 00T6), https://stacks.math.columbia.edu/tag/00T6 ; Lemma 10.137.6 (Tag 00T7), https://stacks.math.columbia.edu/tag/00T7 ; Definition 10.143.1 and Lemma 10.143.3(6) (Tags 00U0 and 00U2), https://stacks.math.columbia.edu/tag/00U0 and https://stacks.math.columbia.edu/tag/00U2 ; Lemma 10.143.5(2) (Tag 00U4), https://stacks.math.columbia.edu/tag/00U4 ; Lemma 10.140.3 (Tag 00TT), https://stacks.math.columbia.edu/tag/00TT ; Lemma 10.106.2 (Tag 00NP), https://stacks.math.columbia.edu/tag/00NP . This auxiliary is a local elimination consequence: the square augmented Jacobian makes the projection to the centered linear coordinates étale near a. The local component is a domain with fraction field finite over the rational-function field in those coordinates. A minimal-polynomial relation for the nonzero class of P has nonzero constant coefficient; clearing its coefficient denominators and then the localization denominator gives H Q(t) in J+(P), with H(a) nonzero. The conversion to this explicit polynomial certificate is part of the Open obligation, not an already formalized or verbatim assertion of those source lemmas.

import Mathlib
set_option autoImplicit false
open scoped BigOperators

namespace AffineJacobian

theorem exists_eliminant_of_nonzero_local_class
    (K σ : Type*) [Field K] [Fintype σ]
    (r d : ℕ) (F : Fin r → MvPolynomial σ K) (a : σ → K)
    (m : MaximalSpectrum (MvPolynomial σ K))
    (hm : m.asIdeal = RingHom.ker (MvPolynomial.eval a))
    (hF : ∀ i, MvPolynomial.eval a (F i) = 0)
    (c : Fin d → σ → K)
    (L : (σ → K) ≃ₗ[K] ((Fin r → K) × (Fin d → K)))
    (hL : ∀ v, L v =
      ((fun i => ∑ j, MvPolynomial.eval a (MvPolynomial.pderiv j (F i)) * v j),
       (fun i => ∑ j, c i j * v j)))
    (P : MvPolynomial σ K)
    (hP : algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal) P ∉
      (Ideal.span (Set.range F)).map
        (algebraMap (MvPolynomial σ K) (Localization.AtPrime m.asIdeal))) :
    ∃ (Q : MvPolynomial (Fin d) K) (H : MvPolynomial σ K),
      Q ≠ 0 ∧ MvPolynomial.eval a H ≠ 0 ∧
      H * MvPolynomial.aeval (fun i => ∑ j,
        MvPolynomial.C (c i j) * (MvPolynomial.X j - MvPolynomial.C (a j))) Q ∈
          Ideal.span (Set.range F) ⊔ Ideal.span {P} := by sorry

end AffineJacobian
