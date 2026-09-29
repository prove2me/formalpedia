-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
-- name    : CerednikDrinfeld.FormalOmega.existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/c2a3ad15-b5fe-5d90-9ce0-837ff452a5b1
-- title:
--   Unique extension of a natural family on Noetherian connected test algebras
-- statement:
--   Fix a prime $r$ and a complete discrete valuation ring $\mathcal O$ which is a domain of characteristic zero, with uniformiser $\pi$ (irreducible, with $\mathcal O$ $\pi$-adically complete), residue ring of cardinality $r$ and $(r)=(\pi)$; let $K_0$ be its fraction field. Let $Onr$ be an $\mathcal O$-algebra which is a domain of characteristic zero, $\pi$-adically complete, with $\pi Onr$ maximal, such that every element of $Onr$ satisfies a monic polynomial over $\mathcal O$ modulo $\pi Onr$ and every monic polynomial over $Onr$ of positive degree has a root modulo $\pi Onr$. Let $f_N : N \to \operatorname{Spec}\mathcal O$ be any scheme over $\mathcal O$. Write $F(B) = (Onr \to_{\mathcal O} B) \times \mathrm{DeligneDatum}(K_0,\pi,B)$, a Deligne datum being a family of $B$-submodules of the base changes of the full lattices in $K_0^2$ with invertible quotients, compatible with inclusions and homotheties and nondegenerate at every prime of $B$, and write $\hat N(B)$ for the set of morphisms $\operatorname{Spec} B \to N$ over $\mathcal O$. Suppose given maps $u_B : F(B) \to \hat N(B)$ for all Noetherian $\mathcal O$-algebras $B$ in which $\pi$ is nilpotent and whose only idempotents are $0$ and $1$, natural for $\mathcal O$-algebra maps between such $B$. Then there is a unique family $U_B : F(B) \to \hat N(B)$, defined for all $\mathcal O$-algebras $B$ with $\pi$ nilpotent, natural for all $\mathcal O$-algebra maps, with $U_B = u_B$ on Noetherian $B$ with only trivial idempotents.
--
--   This is the passage from a natural transformation defined only on Noetherian test algebras with connected spectrum to one defined on all $\pi$-nilpotent test algebras, used in the Čerednik–Drinfeld comparison to produce morphisms from the formal functor $(Onr \to \cdot) \times \hat\Omega$ to a formal scheme over $\mathcal O$. It is invoked by the variant with an extra constant factor and by the constructions of tower families attached to the coarse and fine moduli properties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]
    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr]
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u B' hB' hc' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x)) :
    ∃! U : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
          U B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), U B hB x = u B hB hc x) := by sorry
