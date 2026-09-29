-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
-- name    : AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9007f367-deca-5724-91db-6566d83397d7
-- title:
--   Deuring reduction of divisors at good constant reduction
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with residue field $k$, and let $F/L$ and $\bar F/k$ be fields satisfying `IsCurveOver` (every nonzero element has a finitely supported divisor of degree $0$ recording its orders at all places, all residue fields of places are finite over the constant field, and the module of Kähler differentials is free of rank $1$). Given a valuation subring $\mathcal O\subseteq F$ and a ring homomorphism $\mathrm{res}:\mathcal O\to\bar F$ such that for $c\in L$ one has $c\in\mathcal O$ exactly when $c\in A$, $\mathrm{res}$ is surjective with kernel the maximal ideal of $\mathcal O$, $\mathrm{res}$ agrees on $A$ with the residue map $A\to k$ followed by $k\to\bar F$, and every nonzero $f\in F$ admits $c\in L$ with $cf\in\mathcal O$ and $\mathrm{res}(cf)\neq 0$; assume further that some $x\in\mathcal O$ has $\mathrm{res}(x)$ transcendental over $k$ with $0<[\bar F:k(\mathrm{res}\,x)]$ and $[F:L(x)]=[\bar F:k(\mathrm{res}\,x)]$, and that $\mathrm{genusFF}(k,\bar F)=\mathrm{genusFF}(L,F)$, i.e. the two finranks of $H^1(0)$ agree. Then there is a map $r$ from places of $F/L$ to places of $\bar F/k$ such that for every $f\in\mathcal O$ with $\mathrm{res}(f)\neq 0$, every divisor $D$ with $D(P)=\mathrm{ord}_P(f)$ for all $P$, and every place $Q$ of $\bar F/k$, the pushforward satisfies $(r_*D)(Q)=\mathrm{ord}_Q(\mathrm{res}\,f)$. Here a place is a valuation subring containing the constants, distinct from the whole field and a principal ideal ring, and $\mathrm{ord}$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This is Deuring's theorem on reduction of divisors at a place of good constant reduction: when the genus is preserved, the divisor of a function with nonzero reduction pushes forward to the divisor of its reduction. It is used downstream in the comparison of orders under constant field extension, in the construction of good constant reductions from Witt-vector normal form data, and in the reduction of places of modular curves modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_placeMap_mapDomain_eq_ord_of_good_constantReduction.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.exists_placeMap_mapDomain_eq_ord_of_good_constantReduction
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] [IsCurveOver L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [IsCurveOver (IsLocalRing.ResidueField A) Fbar]
    (O : ValuationSubring F) (res : O →+* Fbar)
    (hOA : ∀ c : L, algebraMap L F c ∈ O ↔ c ∈ A)
    (hsurj : Function.Surjective res)
    (hker : RingHom.ker res = IsLocalRing.maximalIdeal O)
    (hconst : ∀ a : A, res ⟨algebraMap L F a, (hOA a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (he : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ O, res ⟨c • f, h⟩ ≠ 0)
    (hreg : ∃ x : O, Transcendental (IsLocalRing.ResidueField A) (res x) ∧
      0 < Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar ∧
      Module.finrank (IntermediateField.adjoin L ({(x : F)} : Set F)) F =
        Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A) ({res x} : Set Fbar)) Fbar)
    (hgood : genusFF (IsLocalRing.ResidueField A) Fbar = genusFF L F) :
    ∃ r : Place L F → Place (IsLocalRing.ResidueField A) Fbar,
      ∀ f : O, res f ≠ 0 → ∀ D : Divisor L F, (∀ P, D P = P.ord (f : F)) →
        ∀ Q, Finsupp.mapDomain r D Q = Q.ord (res f) := by sorry
