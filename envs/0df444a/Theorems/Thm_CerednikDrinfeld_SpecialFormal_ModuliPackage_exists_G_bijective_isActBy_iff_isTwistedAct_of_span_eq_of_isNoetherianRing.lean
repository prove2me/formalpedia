-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/8cc276c2-3fe7-5bc6-a346-723379bd55a7
-- title:
--   Drinfeld uniformisation of ̄ G_Φ over a Noetherian base
-- statement:
--   Let $r$ be a prime. Let $\mathcal O$ be a characteristic-zero domain which is a discrete valuation ring, $\pi\in\mathcal O$ irreducible, $\mathcal O$ $\pi$-adically complete, with $\#(\mathcal O/\pi)=r$ and $(r)=(\pi)$, and let $K_0$ be a characteristic-zero field that is a fraction field of $\mathcal O$. Let $O^{\mathrm{nr}}$ be a characteristic-zero domain which is an $\mathcal O$-algebra, $\pi$-adically complete, with $\pi O^{\mathrm{nr}}$ maximal, such that every element of $O^{\mathrm{nr}}$ satisfies some monic polynomial over $\mathcal O$ modulo $\pi$ and every monic polynomial over $O^{\mathrm{nr}}$ of positive degree has a root modulo $\pi$, and let $\mathrm{Fr}$ be an $\mathcal O$-algebra automorphism of $O^{\mathrm{nr}}$ with $\mathrm{Fr}(x)\equiv x^r \pmod \pi$. Let $v\!\det:GL_2(K_0)\to\mathbb Z$ (written multiplicatively) be a homomorphism with $v\!\det(g)=n$ exactly when $\det g=u\pi^n$ for some $u\in\mathcal O^\times$. The assertion is the existence of: a ring homomorphism $\iota:W(\mathbb F_{r^2})\to O^{\mathrm{nr}}$; a formal $\mathcal O_D$-module $\Phi$ over $O^{\mathrm{nr}}/r$ that is special for $\iota$ reduced mod $r$ (the Lie algebra splits into the $\iota$- and $\iota\circ\mathrm{Frob}$-eigenparts, both invertible) and has height $4$ (the kernel of multiplication by $r$ is finite projective of rank $r^4$ fibrewise); a moduli package $M$ over $O^{\mathrm{nr}}$ satisfying the Zariski sheaf condition; and a family $\eta$ sending, for every commutative ring $B$ with $\psi:O^{\mathrm{nr}}\to B$ and $r$ nilpotent in $B$, a rigidified datum $t=(X,n,\rho)$ over $B$ to a point of $M(B,\psi)$, such that over Noetherian $B$: $\eta$ identifies two admissible $t,t'$ (i.e. $X$ special for $\psi\circ\iota$ and of height $4$, and $\rho$ an isogeny $\bar\Phi_\psi\to\bar X$ of height $4n$) precisely when they are isomorphic; $\eta$ commutes with base change along ring maps over $O^{\mathrm{nr}}$ for admissible $t$; and every point of $M(B,\psi)$ comes from admissible data after passing to the localisations away from the members of some finite family generating the unit ideal. Moreover there is a ring homomorphism $E_0$ from the centraliser of $\{\Phi.\mathrm{actEnd}\,a\}\cup\{\Phi.\mathrm{varpiEnd}\}$ into $M_2(K_0)$, injective and with $r^mM_2(\mathcal O)\subseteq\operatorname{im}E_0$ and $r^m\operatorname{im}E_0\subseteq M_2(\mathcal O)$ for some $m$, together with maps $e_B$, for every Noetherian $\mathcal O$-algebra $B$ in which $\pi$ is nilpotent, from the set of triples $(\psi:O^{\mathrm{nr}}\to_{\mathcal O}B,\ \text{nilpotence of }r,\ \text{point of }M(B,\psi))$ to $(O^{\mathrm{nr}}\to_{\mathcal O}B)\times\{\text{Deligne data over }B\}$, which are natural in $B$ for $\mathcal O$-algebra maps, bijective for each such $B$, have first component equal to $\psi$, carry the relation $\mathrm{IsActBy}\;\iota\,\Phi\,\eta\,\mathrm{Fr}\,E_0\,g$ (existence of an endomorphism $\epsilon$ of $\Phi$ in that centraliser and $k,m'$ with $E_0\epsilon=r^k g^{-1}$, kernel of $\epsilon$ of degree $r^{2m'}$, and $x'$ the corresponding translate of $x$) exactly to the twisted action of $g$ (first component twisted by $\mathrm{Fr}^{-v\!\det(g)}$, Deligne datum pulled back along $g^{-1}$), send any pair with $\mathrm{IsPiTranslate}\;\iota\,\Phi\,\eta\,\mathrm{Fr}$ to the pair obtained by composing the first component with $\mathrm{Fr}$ and leaving the Deligne datum unchanged, and admit, for every such $x$, some $x'$ with $\mathrm{IsPiTranslate}\;\iota\,\Phi\,\eta\,\mathrm{Fr}\,x\,x'$.
--
--   This is Drinfeld's theorem on the formal moduli of special formal $\mathcal O_D$-modules of height $4$: the functor $\bar G_\Phi$ on $\pi$-nilpotent algebras is identified, compatibly with the $GL_2(K_0)$-action and with the Frobenius translation, with the product of the $O^{\mathrm{nr}}$-points functor and Deligne's formal model of the $p$-adic upper half plane, here over an axiomatically described complete absolutely unramified base $(\mathcal O,\pi,K_0)$ and its completed maximal unramified extension, and with all comparisons asserted over Noetherian test rings only. It feeds the Čerednik–Drinfeld uniformisation of Shimura curves attached to indefinite quaternion algebras, which in turn supplies the local information at the ramified primes in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega
open CerednikDrinfeld.SpecialFormal

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hdvr : IsDiscreteValuationRing 𝒪)
    (π : 𝒪) (hπ : Irreducible π) (hcomplete : IsAdicComplete (Ideal.span {π}) 𝒪)
    (hres : Nat.card (𝒪 ⧸ Ideal.span {π}) = r) (hunr : Ideal.span {((r : ℕ) : 𝒪)} = Ideal.span {π})
    (K₀ : Type) [Field K₀] [CharZero K₀] [Algebra 𝒪 K₀] [IsFractionRing 𝒪 K₀]

    (Onr : Type) [CommRing Onr] [IsDomain Onr] [CharZero Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (hOnr_complete : IsAdicComplete (Ideal.span {algebraMap 𝒪 Onr π}) Onr)
    (hOnr_max : (Ideal.span {algebraMap 𝒪 Onr π}).IsMaximal)
    (hOnr_alg : ∀ x : Onr, ∃ p : Polynomial 𝒪, p.Monic ∧ Polynomial.aeval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hOnr_closed : ∀ p : Polynomial Onr, p.Monic → 0 < p.natDegree → ∃ x : Onr, Polynomial.eval x p ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (hFr : ∀ x : Onr, Fr x - x ^ r ∈ Ideal.span {algebraMap 𝒪 Onr π})
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : 𝒪ˣ, (Matrix.GeneralLinearGroup.det g : K₀) = algebraMap 𝒪 K₀ (u : 𝒪) * (algebraMap 𝒪 K₀ π) ^ n)
    :
    ∃ (ι : Zp2 r →+* Onr)
      (Φ : FormalODModule r (Onr ⧸ pIdeal r Onr))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr)).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r Onr) (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB)
      (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B))
            (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
            (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
        (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr →+* B) (ψ' : Onr →+* B')
            (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
            (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
            η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
            ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
              ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                (hL : IsNilpotent (r : L)),
                ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                  η L ((algebraMap B L).comp ψ) hL t =
                    M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀)
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) 𝒪, ∃ e, E₀ e = (r : K₀) ^ m • A.map (algebraMap 𝒪 K₀)) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪, (r : K₀) ^ m • E₀ e = A.map (algebraMap 𝒪 K₀)))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → (ModuliPackage.G 𝒪 M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π))
          (φ : B →ₐ[𝒪] B') (x : (ModuliPackage.G 𝒪 M).obj B), e B' hB' ((ModuliPackage.G 𝒪 M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr) (Omega K₀ π)).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (ModuliPackage.G 𝒪 M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : (ModuliPackage.G 𝒪 M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct π Onr Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π)) (x x' : (ModuliPackage.G 𝒪 M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist Onr Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 M).obj B), ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by sorry
