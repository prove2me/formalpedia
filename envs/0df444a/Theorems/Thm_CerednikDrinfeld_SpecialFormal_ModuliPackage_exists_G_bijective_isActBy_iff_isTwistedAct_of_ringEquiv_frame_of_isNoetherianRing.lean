-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/8b60c4eb-f38e-5a19-90de-a1f9332b2a61
-- title:
--   Frame change for the descended Drinfeld package on G
-- statement:
--   Throughout, $r$ is a prime.
--
--   **Two frames.** The data of a frame consist of: a commutative ring $\mathcal O$, a field $K_0$ which is an $\mathcal O$-algebra, an element $\pi \in \mathcal O$, an $\mathcal O$-algebra $O^{\mathrm{nr}}$ together with an $\mathcal O$-algebra automorphism $Fr$ of it, and a monoid homomorphism $vdet \colon \mathrm{GL}_2(K_0) \to \mathbb Z$ (written multiplicatively). Two such frames are given, $(\mathcal O, K_0, \pi, O^{\mathrm{nr}}, Fr, vdet)$ and $(\mathcal O', K_0', \pi', O^{\mathrm{nr}\prime}, Fr', vdet')$.
--
--   **Comparison data between the frames.** Ring isomorphisms $eb \colon \mathcal O \simeq \mathcal O'$, $eK \colon K_0 \simeq K_0'$ with $eK(\mathrm{alg}_{\mathcal O \to K_0}(x)) = \mathrm{alg}_{\mathcal O' \to K_0'}(eb\,x)$ for all $x \in \mathcal O$ (`hcomm`); an element $\pi_1 \in \mathcal O'$ with $eb(\pi) = \pi_1$ (`hπ₁`) and $(\pi_1) = (\pi')$ as ideals of $\mathcal O'$ (`hspan`); a ring isomorphism $eO \colon O^{\mathrm{nr}} \simeq O^{\mathrm{nr}\prime}$ compatible with the structure maps through $eb$ (`heO`) and intertwining the two automorphisms, $eO \circ Fr = Fr' \circ eO$ (`hFr`); and the compatibility $vdet'(\mathrm{GL}_2(eK)(g)) = vdet(g)$ for all $g \in \mathrm{GL}_2(K_0)$ (`hv`).
--
--   Here, for a commutative $\mathcal O$-algebra $B$, an object of `OmegaNrObj π Onr B` is a pair consisting of an $\mathcal O$-algebra map $O^{\mathrm{nr}} \to B$ and a Deligne datum: a family of $B$-submodules $\mathrm{line}(M) \subseteq B \otimes_{\mathcal O} M$, indexed by the full lattices $M$ in $K_0^2$, with invertible quotients, monotone and $K_0^\times$-homothety equivariant, and satisfying the non-degeneracy condition at every prime of $B$ that involves $\pi$. For $g \in \mathrm{GL}_2(K_0)$, `IsPullback g d d'` says $d'.\mathrm{line}(M)$ is the pullback of $d.\mathrm{line}(g\cdot M)$ along the base-changed action map, for every $M$; `IsBaseChange f d d'` says $d'.\mathrm{line}(M)$ is the $B'$-span of the image of $d.\mathrm{line}(M)$; and `OmegaNr.IsTwistedAct π Onr Fr vdet B g x x'` says that $x'$ has first component $x.1 \circ Fr^{-vdet(g)}$ and that `IsPullback` holds for $g^{-1}$ on the Deligne-datum components.
--
--   **First transport hypothesis `hΨ`.** There exists a family of bijections $\Psi_B \colon$ `OmegaNrObj π Onr B` $\simeq$ `OmegaNrObj π₁ Onr' B`, indexed by the commutative rings $B$ carrying both an $\mathcal O$- and an $\mathcal O'$-algebra structure whose structure maps agree through $eb$, such that: (i) on first components $\Psi_B(x).1 = x.1 \circ eO^{-1}$; (ii) for all $g$ and all $x, x'$, the twisted action relation for $(\pi_1, O^{\mathrm{nr}\prime}, Fr', vdet')$ at $\mathrm{GL}_2(eK)(g)$ between $\Psi_B(x)$ and $\Psi_B(x')$ holds if and only if it holds for $(\pi, O^{\mathrm{nr}}, Fr, vdet)$ at $g$ between $x$ and $x'$; (iii) the same equivalence for `DeligneDatum.IsPullback` on the second components; and (iv) for any two such rings $B, B_1$ and any $\mathcal O$-algebra map $f \colon B \to B_1$ and $\mathcal O'$-algebra map $f' \colon B \to B_1$ that agree as functions, `DeligneDatum.IsBaseChange` along $f'$ for the transported data holds if and only if it holds along $f$ for the original data.
--
--   **Second transport hypothesis `hΞ`.** There exists a family of bijections $\Xi_B \colon$ `DeligneDatum π₁ B` $\simeq$ `DeligneDatum π' B`, indexed by the commutative $\mathcal O'$-algebras $B$, such that $\Xi_B(d)$ has the same $\mathrm{line}$ function as $d$, and such that `IsPullback` for $\pi'$ between $\Xi_B(d)$ and $\Xi_B(d')$ is equivalent to `IsPullback` for $\pi_1$ between $d$ and $d'$, and likewise for `IsBaseChange` along any $\mathcal O'$-algebra map.
--
--   **The source package `hΞ`–independent hypothesis `hpkg`.** There exist the following data over the first frame. A ring homomorphism $\iota \colon W(\mathbb F_{r^2}) \to O^{\mathrm{nr}}$; a formal $\mathcal O_D$-module $\Phi$ over $O^{\mathrm{nr}}/(r)$ (a $2$-dimensional commutative formal group law with a $W(\mathbb F_{r^2})$-action and a uniformiser endomorphism $\varpi$ satisfying $\varpi \circ \varpi = [r]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$) which is special for the structure map induced by $\iota$ (the zero and one eigen-parts of its Lie module are complementary and invertible) and of height $4$ (the multiplication by $r$ has kernel of degree $r^4$); a moduli package $M$ over $O^{\mathrm{nr}}$ — a functor $B, \psi \colon O^{\mathrm{nr}} \to B, \ r$ nilpotent in $B \mapsto M.\mathrm{obj}$ with functorial transition maps — which is a Zariski sheaf; and a map $\eta$ assigning, for every commutative ring $B$ with $\psi \colon O^{\mathrm{nr}} \to B$ and $r$ nilpotent in $B$, a point of $M.\mathrm{obj}$ to every rigidified object $t = (X, n, \rho)$ over $B$. The three laws required of $\eta$ (stated for Noetherian test rings) are: $\eta$ separates admissible rigidified objects exactly up to isomorphism of rigidified objects; $\eta$ commutes with base change along ring maps compatible with the $O^{\mathrm{nr}}$-structures, for admissible objects; and every point of $M.\mathrm{obj}\,B$ is, locally for a Zariski cover $\mathrm{span}(f_0,\dots,f_{n-1}) = B$, the image under $\eta$ of an admissible rigidified object over each Noetherian localisation away from $f_i$ in which $r$ is nilpotent. Further: a ring homomorphism $E_0$ from the centraliser of $\mathrm{range}(\Phi.\mathrm{actEnd}) \cup \{\Phi.\mathrm{varpiEnd}\}$ in the endomorphisms of $\Phi$ to $M_2(K_0)$, which is injective and commensurable with $M_2(\mathcal O)$ in the sense that for some $m \in \mathbb N$ every $A \in M_2(\mathcal O)$ satisfies $r^m A = E_0(e)$ for some $e$, and $r^m E_0(e)$ lies in the image of $M_2(\mathcal O)$ for every $e$. Finally a map $e$ which, for every Noetherian commutative $\mathcal O$-algebra $B$ in which $\pi$ becomes nilpotent, sends points of the functor `ModuliPackage.G 𝒪 M` at $B$ (triples consisting of an $\mathcal O$-algebra map $\psi \colon O^{\mathrm{nr}} \to B$, a witness that $r$ is nilpotent in $B$, and a point of $M.\mathrm{obj}\,B\,\psi$) to points of the product functor $B \mapsto (O^{\mathrm{nr}} \to_{\mathcal O} B) \times$ `Omega K₀ π` $(B)$, subject to six clauses: $e$ is natural in $B$; each $e_B$ is bijective; the first component of $e_B(x)$ is $x.\psi$; for every $g \in \mathrm{GL}_2(K_0)$ and all $x, x'$, the relation `ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x'` (there exist $e$ in the centraliser and $k, m' \in \mathbb N$ with $E_0(e) = r^k g^{-1}$, the power series of $e$ having kernel of degree $r^{2m'}$, together with the translation relation at level $(k, m')$, which requires $x'.\psi = x.\psi \circ Fr^{\,m' - 2k}$ and, locally on a Zariski cover, admissible rigidified lifts of the two points related by `Rigidified.IsTranslate`) holds if and only if `OmegaNr.IsTwistedAct π Onr Fr vdet B g (e_B x) (e_B x')` holds; the relation `ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'` (namely $x'.\psi = x.\psi \circ Fr$ together with local admissible lifts related by `Rigidified.IsPiTranslate`) implies $e_B(x') = (e_B(x).1 \circ Fr, \ e_B(x).2)$; and every point $x$ of `ModuliPackage.G 𝒪 M` at a Noetherian $\mathcal O$-algebra $B$ admits some $x'$ with `ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'`.
--
--   **Conclusion.** There exist data of exactly the same shape over the second frame: a ring homomorphism $\iota \colon W(\mathbb F_{r^2}) \to O^{\mathrm{nr}\prime}$; a formal $\mathcal O_D$-module $\Phi$ over $O^{\mathrm{nr}\prime}/(r)$, special for the structure map induced by $\iota$ and of height $4$; a moduli package $M$ over $O^{\mathrm{nr}\prime}$ which is a Zariski sheaf; a map $\eta$ from rigidified objects to points of $M$, satisfying the same three laws (separation of admissible objects up to isomorphism, compatibility with base change, and local surjectivity through Noetherian localisations of a Zariski cover); an injective ring homomorphism $E_0$ from the centraliser of $\mathrm{range}(\Phi.\mathrm{actEnd}) \cup \{\Phi.\mathrm{varpiEnd}\}$ to $M_2(K_0')$, commensurable with $M_2(\mathcal O')$ in the same two-sided sense with some exponent $m$; and a map $e$ defined on Noetherian commutative $\mathcal O'$-algebras $B$ in which $\pi'$ becomes nilpotent, from points of `ModuliPackage.G 𝒪' M` to points of $B \mapsto (O^{\mathrm{nr}\prime} \to_{\mathcal O'} B) \times$ `Omega K₀' π'` $(B)$, such that: (1) $e$ is natural with respect to $\mathcal O'$-algebra maps $\varphi \colon B \to B'$ between Noetherian $\mathcal O'$-algebras in which $\pi'$ is nilpotent; (2) each $e_B$ is bijective; (3) the first component of $e_B(x)$ equals $x.\psi$; (4) for every $g \in \mathrm{GL}_2(K_0')$ and all $x, x'$, `ModuliPackage.G.IsActBy ι Φ η Fr' E₀ g x x'` holds if and only if `OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B g (e_B x) (e_B x')` holds; (5) `ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x'` implies $e_B(x') = (\mathrm{frobTwist}\,O^{\mathrm{nr}\prime}\,Fr'\,1\,(e_B(x).1),\ e_B(x).2)$; and (6) every point $x$ of `ModuliPackage.G 𝒪' M` at a Noetherian commutative $\mathcal O'$-algebra $B$ admits some $x'$ with `ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x'` (this last clause, as in the hypothesis, carries no nilpotence assumption on $\pi'$).
--
--   This is the frame-change step in the Čerednik–Drinfeld thread: it moves a descended Drinfeld package — the moduli package of rigidified special formal $\mathcal O_D$-modules together with the natural identification of its $G$-points with the $O^{\mathrm{nr}}$-points of Drinfeld's $p$-adic upper half plane functor — from one presentation of the frame data $(\mathcal O, K_0, \pi; O^{\mathrm{nr}}, Fr; vdet)$ to an isomorphic one, using the prescribed transport of $(O^{\mathrm{nr}} \to -) \times \widehat\Omega$ and the change of uniformiser from $\pi_1 = eb(\pi)$ to $\pi'$, over the category of Noetherian test algebras. It is used by the variant in which the hypotheses on the uniformisers are recorded through the equality of the generated ideals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct
open LT.LatticeTree CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_ringEquiv_frame_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime]

    (𝒪 : Type) [CommRing 𝒪] (K₀ : Type) [Field K₀] [Algebra 𝒪 K₀] (π : 𝒪)
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K₀ →* Multiplicative ℤ)
    (𝒪' : Type) [CommRing 𝒪'] (K₀' : Type) [Field K₀'] [Algebra 𝒪' K₀'] (π' : 𝒪')
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K₀' →* Multiplicative ℤ)

    (eb : 𝒪 ≃+* 𝒪') (eK : K₀ ≃+* K₀') (hcomm : ∀ x : 𝒪, eK (algebraMap 𝒪 K₀ x) = algebraMap 𝒪' K₀' (eb x))
    (π₁ : 𝒪') (hπ₁ : eb π = π₁) (hspan : Ideal.span {π₁} = Ideal.span {π'})
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (eb x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (hv : ∀ g, vdet' (Matrix.GeneralLinearGroup.map eK.toRingHom g) = vdet g)

    (hΨ :
      ∃ (Ψ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B],
          (∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x)) →
            (OmegaNrObj (K := K₀) π Onr B ≃ OmegaNrObj (K := K₀') π₁ Onr' B)),
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (x : OmegaNrObj (K := K₀) π Onr B) (y : Onr'), (Ψ B hB x).1 y = x.1 (eO.symm y)) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          OmegaNr.IsTwistedAct π₁ Onr' Fr' vdet' B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x) (Ψ B hB x') ↔
            OmegaNr.IsTwistedAct π Onr Fr vdet B g x x') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (g : Matrix.GeneralLinearGroup (Fin 2) K₀) (x x' : OmegaNrObj (K := K₀) π Onr B),
          DeligneDatum.IsPullback (K := K₀') (π := π₁) B (Matrix.GeneralLinearGroup.map eK.toRingHom g) (Ψ B hB x).2 (Ψ B hB x').2 ↔
            DeligneDatum.IsPullback (K := K₀) (π := π) B g x.2 x'.2) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
            (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (eb x))
            (B₁ : Type) [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
            (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (eb x))
            (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (_ : ∀ b, f b = f' b)
            (x : OmegaNrObj (K := K₀) π Onr B) (x₁ : OmegaNrObj (K := K₀) π Onr B₁),
          DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f' (Ψ B hB x).2 (Ψ B₁ hB₁ x₁).2 ↔
            DeligneDatum.IsBaseChange (K := K₀) (π := π) f x.2 x₁.2))

    (hΞ :
      ∃ Ξ : ∀ (B : Type) [CommRing B] [Algebra 𝒪' B], DeligneDatum (K := K₀') π₁ B ≃ DeligneDatum (K := K₀') π' B,
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (d : DeligneDatum (K := K₀') π₁ B), (Ξ B d).line = d.line) ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (g : Matrix.GeneralLinearGroup (Fin 2) K₀')
            (d d' : DeligneDatum (K := K₀') π₁ B),
          DeligneDatum.IsPullback (K := K₀') (π := π') B g (Ξ B d) (Ξ B d') ↔
            DeligneDatum.IsPullback (K := K₀') (π := π₁) B g d d') ∧
        (∀ (B : Type) [CommRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [Algebra 𝒪' B'] (f : B →ₐ[𝒪'] B')
            (d : DeligneDatum (K := K₀') π₁ B) (d' : DeligneDatum (K := K₀') π₁ B'),
          DeligneDatum.IsBaseChange (K := K₀') (π := π') f (Ξ B d) (Ξ B' d') ↔
            DeligneDatum.IsBaseChange (K := K₀') (π := π₁) f d d'))

    (hpkg :
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

        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪 B] (x : (ModuliPackage.G 𝒪 M).obj B), ∃ x' : (ModuliPackage.G 𝒪 M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'))
    :
    ∃ (ι : Zp2 r →+* Onr')
      (Φ : FormalODModule r (Onr' ⧸ pIdeal r Onr'))
      (_ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r Onr')).comp ι))
      (_ : Φ.HasHeight 4)
      (M : ModuliPackage.{0, 0} r Onr') (_ : M.IsZariskiSheaf)
      (η : ∀ (B : Type) [CommRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)),
        Rigidified r Φ B → M.obj B ψ hB)
      (_ : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B))
            (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
            (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
        (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : Onr' →+* B) (ψ' : Onr' →+* B')
            (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
            (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
            η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
        (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : Onr' →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
            ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
              ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
                (hL : IsNilpotent (r : L)),
                ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                  η L ((algebraMap B L).comp ψ) hL t =
                    M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K₀')
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) 𝒪', ∃ e, E₀ e = (r : K₀') ^ m • A.map (algebraMap 𝒪' K₀')) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) 𝒪', (r : K₀') ^ m • E₀ e = A.map (algebraMap 𝒪' K₀')))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B], IsNilpotent (algebraMap 𝒪' B π') → (ModuliPackage.G 𝒪' M).obj B → (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra 𝒪' B'] (hB : IsNilpotent (algebraMap 𝒪' B π')) (hB' : IsNilpotent (algebraMap 𝒪' B' π'))
          (φ : B →ₐ[𝒪'] B') (x : (ModuliPackage.G 𝒪' M).obj B), e B' hB' ((ModuliPackage.G 𝒪' M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep Onr') (Omega K₀' π')).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x : (ModuliPackage.G 𝒪' M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (g : Matrix.GeneralLinearGroup (Fin 2) K₀') (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr' E₀ g x x' ↔ OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (hB : IsNilpotent (algebraMap 𝒪' B π')) (x x' : (ModuliPackage.G 𝒪' M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x' → e B hB x' = (frobTwist Onr' Fr' 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra 𝒪' B] (x : (ModuliPackage.G 𝒪' M).obj B), ∃ x' : (ModuliPackage.G 𝒪' M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr' x x') := by sorry
