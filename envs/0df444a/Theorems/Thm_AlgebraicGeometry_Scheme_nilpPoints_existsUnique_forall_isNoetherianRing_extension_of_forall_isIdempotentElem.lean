-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
-- name    : AlgebraicGeometry.Scheme.nilpPoints.existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/7ae7c22a-84d8-5893-918f-93a895a93fd3
-- title:
--   Unique natural extension from connected Noetherian test algebras
-- statement:
--   Let $\mathcal O$ be a commutative ring, $\pi\in\mathcal O$, and let $F$ be an `AlgFunctor` over $\mathcal O$, that is, an assignment of a type $F(B)$ to every commutative $\mathcal O$-algebra $B$ together with maps $F(\varphi):F(B)\to F(B')$ for $\mathcal O$-algebra homomorphisms $\varphi$, compatible with identities and composition. Let $N$ be a scheme and $f_N:N\to\operatorname{Spec}\mathcal O$ a morphism; write $\hat N(B)$ for $(\mathtt{Scheme.nilpPoints}\,f_N).obj\,B$, the set of morphisms $\phi:\operatorname{Spec}B\to N$ such that $\phi$ followed by $f_N$ equals $\operatorname{Spec}$ of the structure map $\mathcal O\to B$, functorial in $B$ by precomposition with $\operatorname{Spec}$ of the given algebra homomorphism. Suppose given, for every Noetherian commutative $\mathcal O$-algebra $B$ in which the image of $\pi$ is nilpotent and whose only idempotents are $0$ and $1$, a map $u_B:F(B)\to\hat N(B)$, and suppose these are natural: for all such $B,B'$ and every $\mathcal O$-algebra homomorphism $\varphi:B\to B'$ and $x\in F(B)$, one has $u_{B'}(F(\varphi)x)=\hat N(\varphi)(u_B x)$. Then there is a unique family $U_B:F(B)\to\hat N(B)$, indexed by all Noetherian commutative $\mathcal O$-algebras $B$ with $\pi$ nilpotent in $B$ (no condition on idempotents), which is natural in the same sense and satisfies $U_B=u_B$ whenever the idempotents of $B$ are only $0$ and $1$.
--
--   This is the existence half of the extension principle for natural families of $\mathcal O$-points of a scheme defined only on test algebras with connected spectrum: the uniqueness assertion rests on [`AlgebraicGeometry.Scheme.nilpPoints.forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem`](thm.html#AlgebraicGeometry.Scheme.nilpPoints.forall_isNoetherianRing_eq_of_forall_eq_of_forall_isIdempotentElem), and the decomposition of a Noetherian spectrum into finitely many clopen pieces cut out by idempotents supplies the gluing. It is used by [`CerednikDrinfeld.FormalOmega.existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem`](thm.html#CerednikDrinfeld.FormalOmega.existsUnique_extension_of_isNoetherianRing_of_forall_isIdempotentElem) in the construction of morphisms into the formal models occurring in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_nilpPoints_existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld.FormalOmega

theorem AlgebraicGeometry.Scheme.nilpPoints.existsUnique_forall_isNoetherianRing_extension_of_forall_isIdempotentElem
    {𝒪 : Type} [CommRing 𝒪] (π : 𝒪) (F : AlgFunctor 𝒪)
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) → F.obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (hc' : ∀ e : B', IsIdempotentElem e → e = 0 ∨ e = 1)
      (φ : B →ₐ[𝒪] B') (x : F.obj B),
      u B' hB' hc' (F.map φ x) = (Scheme.nilpPoints fN).map φ (u B hB hc x)) :
    ∃! U : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → F.obj B → (Scheme.nilpPoints fN).obj B,

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : F.obj B),
          U B' hB' (F.map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
          (hc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (x : F.obj B), U B hB x = u B hB hc x) := by sorry
