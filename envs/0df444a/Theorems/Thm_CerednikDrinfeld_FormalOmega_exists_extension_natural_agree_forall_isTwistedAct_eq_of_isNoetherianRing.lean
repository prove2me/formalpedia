-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalOmega_exists_extension_natural_agree_forall_isTwistedAct_eq_of_isNoetherianRing
-- name    : CerednikDrinfeld.FormalOmega.exists_extension_natural_agree_forall_isTwistedAct_eq_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.225785+00:00
-- url     : https://prove2.me/theorems/870140f1-3bb0-5fbb-9bf5-724c4bd1cc67
-- title:
--   Extension of natural families from Noetherian to all π-nilpotent algebras
-- statement:
--   Fix a prime $r$ and a complete discrete valuation ring $\mathcal O$ which is a domain of characteristic zero, with uniformiser $\pi$ (irreducible, $\mathcal O$ being $\pi$-adically complete), residue ring of cardinality $r$ and $(r)=(\pi)$; let $K_0$ be a fraction field of $\mathcal O$, and $O^{\mathrm{nr}}$ an $\mathcal O$-algebra which is a domain of characteristic zero, $\pi$-adically complete, with $(\pi)$ maximal, such that every element of $O^{\mathrm{nr}}$ satisfies a monic polynomial over $\mathcal O$ modulo $\pi$ and every monic polynomial of positive degree over $O^{\mathrm{nr}}$ has a root modulo $\pi$. Let $Fr$ be an $\mathcal O$-algebra automorphism of $O^{\mathrm{nr}}$, $v_{\det}\colon GL_2(K_0)\to\mathbb Z$ a homomorphism, $G$ a group, and $f_N\colon N\to\operatorname{Spec}\mathcal O$ a scheme over $\mathcal O$. Write $F(B)=\bigl((O^{\mathrm{nr}}\to_{\mathcal O} B)\times \hat\Omega(B)\bigr)\times G$, where $\hat\Omega(B)$ is the set of Deligne data over $B$ (a family of $B$-lines in the base changes of the full lattices of $K_0^2$, with invertible quotients, compatible with inclusions and homotheties, and nondegenerate at every prime), and $\hat N(B)=\{\varphi\colon\operatorname{Spec}B\to N \mid \varphi\text{ over }\operatorname{Spec}\mathcal O\}$. Given $u_B\colon F(B)\to \hat N(B)$ for all Noetherian $\mathcal O$-algebras $B$ in which $\pi$ is nilpotent, natural for $\mathcal O$-algebra maps between such $B$, the assertion is that there exists $U_B\colon F(B)\to\hat N(B)$ defined for all $\mathcal O$-algebras $B$ with $\pi$ nilpotent, natural for all $\mathcal O$-algebra maps, such that: $U_B=u_B$ for every Noetherian such $B$; for each $\gamma\in GL_2(K_0)$ and $c\in G$, if $u_B(x',cg)=u_B(x,g)$ holds whenever $x,x'$ satisfy `OmegaNr.IsTwistedAct` for $\gamma$ (that is, $x'$ has first component the $Fr$-twist of that of $x$ by $-v_{\det}(\gamma)$ and second component the pullback of that of $x$ along $\gamma^{-1}$), for all Noetherian $B$ with only the trivial idempotents, then the same identity holds for $U$ over every $\pi$-nilpotent $B$; and for each $h\colon N\to N$ over $\operatorname{Spec}\mathcal O$ and $c\in G$, if $u_B(x,gc)$ followed by $h$ equals $u_B(x,g)$ for all Noetherian $B$ with only the trivial idempotents, then $U_B(x,gc)$ followed by $h$ equals $U_B(x,g)$ over every $\pi$-nilpotent $B$.
--
--   This is the passage from the Noetherian level to the whole category of $\pi$-nilpotent $\mathcal O$-algebras for families of points of a scheme over $\mathcal O$ parametrised by the functor of Deligne data with unramified coefficients and a group factor, together with the transfer of the twisted $GL_2(K_0)$-equivariance relations and of the relations given by $\mathcal O$-endomorphisms of the target. It is used in the fine moduli statements for the Čerednik–Drinfeld uniformisation, where families constructed over Noetherian bases with connected spectrum must be recognised on all of the formal category.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalOmega_exists_extension_natural_agree_forall_isTwistedAct_eq_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_AlgFunctorConst

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry CerednikDrinfeld
open CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.FormalOmega.exists_extension_natural_agree_forall_isTwistedAct_eq_of_isNoetherianRing
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

    (Fr : Onr ≃ₐ[𝒪] Onr) (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (G : Type) [Group G]
    {N : Scheme.{0}} (fN : N ⟶ Spec (CommRingCat.of 𝒪))

    (u : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) →
      (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fN).obj B)
    (hu : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B']
      (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
      (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
      u B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fN).map φ (u B hB x))
    :
    ∃ U : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B → (Scheme.nilpPoints fN).obj B,

      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B']
          (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (φ : B →ₐ[𝒪] B') (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          U B' hB' ((AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).map φ x) = (Scheme.nilpPoints fN).map φ (U B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (AlgFunctor.prod (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)) (AlgFunctor.const G)).obj B),
          U B hB x = u B hB x) ∧

      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K₀) (c : G),
          (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
              (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) →
              ∀ (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
                OmegaNr.IsTwistedAct π Onr Fr vdet B γ x x' → u B hB (x', c * g) = u B hB (x, g)) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x x' : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
            OmegaNr.IsTwistedAct π Onr Fr vdet B γ x x' → U B hB (x', c * g) = U B hB (x, g)) ∧

      (∀ (h : N ⟶ N) (w : h ≫ fN = fN) (c : G),
          (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)),
              (∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) →
              ∀ (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
                (Scheme.nilpPoints.mapHom fN fN h w).app B (u B hB (x, g * c)) = u B hB (x, g)) →
          ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
            (x : (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B) (g : G),
            (Scheme.nilpPoints.mapHom fN fN h w).app B (U B hB (x, g * c)) = U B hB (x, g)) := by sorry
