-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws
-- name    : CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/285f3734-4ebb-53ea-a75c-3cd73ca7e5b0
-- title:
--   Action laws for the twisted GL₂(K₀)-relation on Ω
-- statement:
--   Fix a commutative ring $\mathcal{O}$, a field $K_0$ that is an $\mathcal{O}$-algebra, an element $\pi\in\mathcal{O}$, a commutative $\mathcal{O}$-algebra $Onr$ with an $\mathcal{O}$-algebra automorphism $Fr$, and a monoid homomorphism $vdet:\mathrm{GL}_2(K_0)\to\mathbb{Z}$ (written multiplicatively). Consider the functor on $\mathcal{O}$-algebras whose value at $B$ is the product $(Onr\to_{\mathcal{O}}B)\times\mathrm{DeligneDatum}$, i.e. pairs $x=(\psi,P)$ with $\psi$ an $\mathcal{O}$-algebra map and $P$ a Deligne datum over $B$, and whose map along $\varphi:B\to B'$ sends $(\psi,P)$ to $(\varphi\circ\psi,\ \varphi_*P)$, the second component having lines the $B'$-spans of the images of the lines of $P$ under $\varphi\otimes\mathrm{id}$. For $g\in\mathrm{GL}_2(K_0)$ the relation `OmegaNr.IsTwistedAct` holds of $x,x'$ when $x'$ has first component $\psi\circ Fr^{-vdet(g)}$ and second component the pullback of $P$ along $g^{-1}$, meaning that for every full lattice $M$ the line of $x'_2$ at $M$ is the preimage of the line of $P$ at $g^{-1}M$ under the base-changed lattice isomorphism. The theorem asserts the conjunction of eight statements, each universally quantified over $\mathcal{O}$-algebras $B$: this relation is functional in $x'$; it is total, i.e. some $x'$ always exists; $g=1$ relates $x$ to itself; relating $x$ to $y$ by $g$ and $y$ to $z$ by $g'$ relates $x$ to $z$ by $g'g$; it is preserved by the functor's map along any $\mathcal{O}$-algebra map $\varphi:B\to B'$; the twist by $-vdet(g'g)$ equals the twist by $-vdet(g')$ of the twist by $-vdet(g)$ on any $\psi:Onr\to_{\mathcal{O}}B$; every Deligne datum over $B$ admits a pullback along $g^{-1}$; and pullback along $g^{-1}$ followed by pullback along $g'^{-1}$ agrees with pullback along $(g'g)^{-1}$.
--
--   These are the axioms needed to recognise the twisted $\mathrm{GL}_2(K_0)$-relation on the product of the Drinfeld-type functor of Deligne data with the corepresentable functor of $\mathcal{O}^{\mathrm{nr}}$-points as the graph of a genuine group action, the action appearing in the Čerednik–Drinfeld uniformisation. The eight clauses are consumed directly by the formal-quotient and descent results for this functor, such as the uniqueness statement [`CerednikDrinfeld.FormalOmega.OmegaNr.forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem`](thm.html#CerednikDrinfeld.FormalOmega.OmegaNr.forall_eq_of_isTwistedAct_of_forall_isNoetherianRing_of_forall_isIdempotentElem) and the descended-quotient lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_OmegaNr_isTwistedAct_laws.lean

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.OmegaNr.isTwistedAct_laws
    {𝒪 : Type} [CommRing 𝒪] {K₀ : Type} [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ) :
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' x'' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B g x x'' → x' = x'') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      ∃ x', OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B), OmegaNr.IsTwistedAct π Onr Fr vdet B 1 x x) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (x y z : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x y → OmegaNr.IsTwistedAct π Onr Fr vdet B g' y z →
      OmegaNr.IsTwistedAct π Onr Fr vdet B (g' * g) x z) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B')
      (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' → OmegaNr.IsTwistedAct π Onr Fr vdet B' g ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x) ((AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ x')) ∧

    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (ψ : Onr →ₐ[𝒪] B),
      frobTwist Onr Fr (- Multiplicative.toAdd (vdet (g' * g))) ψ =
        frobTwist Onr Fr (- Multiplicative.toAdd (vdet g')) (frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) ψ)) ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (P : (Omega K₀ π).obj B),
      ∃ P', DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P') ∧
    (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g g' : Matrix.GeneralLinearGroup (Fin 2) K₀) (P P' P'' : (Omega K₀ π).obj B),
      DeligneDatum.IsPullback (K := K₀) (π := π) B g⁻¹ P P' → DeligneDatum.IsPullback (K := K₀) (π := π) B g'⁻¹ P' P'' →
      DeligneDatum.IsPullback (K := K₀) (π := π) B (g' * g)⁻¹ P P'') := by sorry
