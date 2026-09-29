-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem
-- name    : CerednikDrinfeld.FormalOmega.OmegaNr.forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/083df84a-710c-547c-9774-f972721f206a
-- title:
--   Descent of a twisted-action relation to all π-nilpotent algebras
-- statement:
--   Fix a commutative ring $\mathcal O$, a field $K_0$ which is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, a commutative $\mathcal O$-algebra $O^{\mathrm{nr}}$ with an $\mathcal O$-algebra automorphism $\mathrm{Fr}$, a monoid homomorphism $v_{\det} : \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively), a scheme $N$ with a morphism $f_N : N \to \operatorname{Spec}\mathcal O$, and $g \in \mathrm{GL}_2(K_0)$. Let $F$ be the functor on $\mathcal O$-algebras sending $B$ to $(O^{\mathrm{nr}} \to_{\mathcal O} B) \times \mathrm{DeligneDatum}(\pi, B)$, the product of the functor corepresented by $O^{\mathrm{nr}}$ with `Omega K₀ π`. Assume: (i) for every $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent, every point of $F(B)$ is the image under $F$ of a point of $F(S)$ for some Noetherian $\mathcal O$-subalgebra $S \subseteq B$; (ii) $u_1, u_2$ assign to each such $B$ and each point of $F(B)$ a morphism $\operatorname{Spec} B \to N$ whose composite with $f_N$ is the structure morphism $\operatorname{Spec} B \to \operatorname{Spec}\mathcal O$, compatibly with all $\mathcal O$-algebra maps $\varphi : B \to B'$ between $\pi$-nilpotent algebras; (iii) for every Noetherian such $B$ whose only idempotents are $0$ and $1$, and all $x = (\psi,d)$, $x' = (\psi',d')$ in $F(B)$ with $\psi' = \psi \circ \mathrm{Fr}^{-v_{\det}(g)}$ and $d'$ the pullback of $d$ along $g^{-1}$ (i.e. $d'.\mathrm{line}\,M$ is the preimage of $d.\mathrm{line}(g^{-1}M)$ under the base-changed action isomorphism, for every full lattice $M$), one has $u_1(x') = u_2(x)$. The conclusion is that this last implication holds for every $\pi$-nilpotent $\mathcal O$-algebra $B$, with no Noetherian or connectedness hypothesis.
--
--   This is the globalisation step for the twisted $\mathrm{GL}_2(K_0)$-action on the unramified-base-point functor times the formal upper half plane functor: a relation between two natural families of $N$-valued points, verified only over Noetherian bases with trivial idempotents, is extended to arbitrary $\pi$-nilpotent bases. It is used in the construction of the Čerednik–Drinfeld fine family and its Atkin–Lehner compatibility.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_OmegaNr_forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.OmegaNr.forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (hF : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      ∀ x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
      ∃ (S : Subalgebra 𝒪 B) (_ : IsNoetherianRing ↥S) (x₀ : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj ↥S),
        (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map S.val x₀ = x)
    (g : Matrix.GeneralLinearGroup (Fin 2) K₀)

    (u₁ u₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B → (Scheme.nilpPoints fN).obj B)
    (hu₁ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u₁ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u₁ B hB x))
    (hu₂ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B')
      (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      u₂ B' hB' ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) = (Scheme.nilpPoints fN).map φ (u₂ B hB x))

    (hrel : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) →
      ∀ x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B,
        OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → u₁ B hB x' = u₂ B hB x) :
    ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
      (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → u₁ B hB x' = u₂ B hB x := by sorry
