-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/721b005c-ed61-5155-b64d-f880bd98f441
-- title:
--   Equivariant gluing of G_Φ with Ω̂ over Noetherian bases
-- statement:
--   Fix a prime $r$ and an algebraically closed field $k$ of characteristic $r$, and let $W(k) =$ `WittVector r k` carry a $\mathbb{Z}_r$-algebra structure.
--
--   **Frame data.** $Fr$ is a $\mathbb{Z}_r$-algebra automorphism of $W(k)$, and the hypothesis `hFr` says that $Fr$ agrees pointwise with `WittVector.frobenius`. Further, $vdet$ is a monoid homomorphism from $\mathrm{GL}_2(\mathbb{Q}_r)$ to $\mathbb{Z}$ written multiplicatively, and the hypothesis `hvdet` pins it down: $vdet\,g = n$ if and only if $\det g = u\, r^{n}$ in $\mathbb{Q}_r$ for some unit $u$ of $\mathbb{Z}_r$; thus $vdet$ is the $r$-adic valuation of the determinant.
--
--   **The special formal module.** $\iota$ is a ring homomorphism from $\mathbb{Z}_{r,2} := W(\mathbb{F}_{r^2})$ (the Lean `Zp2 r`) to $W(k)$, and $\Phi$ is a `FormalODModule r` over $W(k)/(r)$, that is, a commutative two‑dimensional formal group law together with an action of $\mathbb{Z}_{r,2}$ and an endomorphism $\varpi$ satisfying $\varpi\circ\varpi = [r]$ and $\varpi\circ [a] = [\sigma(a)]\circ\varpi$. The hypothesis $h\Phi$ asserts `IsSpecial` for the structure map obtained from $\iota$ followed by reduction modulo $r$: the two eigen-submodules `lieZero` and `lieOne` of the Lie module are complementary and each invertible. The hypothesis $h\Phi 4$ asserts `HasHeight 4`, i.e. the kernel algebra of $[r]$ on $\Phi$ is finite projective of rank $r^4$ at every field-valued point.
--
--   **The moduli package.** $M$ is a `ModuliPackage.{0,0} r (WittVector r k)`: a family of types $M.obj\,B\,\psi\,h_B$ indexed by commutative rings $B$ in which $r$ is nilpotent together with a ring homomorphism $\psi : W(k)\to B$, functorial in $B$ along $W(k)$-compatible ring maps. The hypothesis $hM$ asserts `IsZariskiSheaf`: separatedness and glueing for finite Zariski covers by localisations away from a family generating the unit ideal. The datum $\eta$ assigns to every $B$, $\psi$, nilpotence witness $h_B$, and rigidified object $t \in$ `Rigidified r Φ B` (a formal $\mathcal{O}_D$-module $t.X$ over $B$, a natural number $t.n$, and a series $t.\rho$ over $B/(r)$) a point of $M.obj\,B\,\psi\,h_B$.
--
--   The hypothesis $h\eta$ has three clauses, all over Noetherian $B$: (i) for admissible $t,t'$ over the same $\psi$ (admissibility: $t.X$ is special for the structure map attached to $\iota,\psi$, has height $4$, and $t.\rho$ is an isogeny of height $4t.n$ from the reduction of $\Phi$ to $\bar t.X$), one has $\eta\,t = \eta\,t'$ if and only if $t$ and $t'$ are isomorphic in the sense of `Rigidified.IsIsomorphic`; (ii) $\eta$ is compatible with ring maps $f : B\to B'$ satisfying $f\circ\psi = \psi'$, applied to admissible $t$; (iii) every point $m$ of $M.obj\,B\,\psi\,h_B$ is, Zariski-locally, of the form $\eta\,t$ for admissible $t$: there are finitely many $f_i \in B$ generating the unit ideal such that over each localisation $L$ away from $f_i$ with $r$ nilpotent in $L$, some admissible $t$ over $L$ has $\eta\,t$ equal to the image of $m$.
--
--   **The hypothesis `hmaster`.** It asserts the existence of a family $\theta$, assigning to each Noetherian $\mathbb{Z}_r$-algebra $B$ with $r$ nilpotent and each $\psi$ a map from $M.obj\,B\,\psi\,h_B$ to `OmegaObj` at $\pi = r$ (Deligne data over $B$: a line `line M` in $B\otimes_{\mathbb{Z}_r} M$ for every full lattice $M$ in $\mathbb{Q}_r^2$, with invertible quotient, monotone in $M$, equivariant for scalar homotheties, and non-degenerate at every prime of $B$), and of a ring homomorphism $E$ from the centralizer of $\{\Phi.\mathrm{actEnd}\ a\}\cup\{\Phi.\mathrm{varpiEnd}\}$ inside the endomorphisms of $\Phi.F$ to $M_2(\mathbb{Q}_r)$, subject to seven clauses: (a) each $\theta\,B\,\psi\,h_B$ is bijective; (b) for a $\mathbb{Z}_r$-algebra map $f : B\to B'$ with $f\circ\psi = \psi'$, the datum $\theta\,B'\,\psi'$ of the transported point is the base change along $f$ of $\theta\,B\,\psi$ of the point, in the sense of `DeligneDatum.IsBaseChange`; (c) $E$ is injective and there is $m$ with $r^m A$ in the image of $E$ for every $A \in M_2(\mathbb{Z}_r)$ and with $r^m E(e)$ integral for every $e$ — so the image of $E$ is commensurable with $M_2(\mathbb{Z}_r)$; (d) existence of translates: for Noetherian $B$, $\psi$, admissible $t$, an element $e$ of the centralizer and $m'$ with the kernel of $e$ of degree $r^{2m'}$, there is a rigidified $t'$ admissible for $\psi\circ\mathrm{Frob}^{m'}$ with $t'.X = t.X$ and, for some $c$, the identity $(\bar t.X.\mathrm{act}\,r^{c+t.n})\circ\bigl(t'.\rho\circ(X_i\mapsto X_i^{r^{m'}})\bigr) = (\bar t.X.\mathrm{act}\,r^{c+t'.n})\circ\bigl(t.\rho\circ \bar e\bigr)$, where $\bar e$ is the power series of $e$ reduced along $\psi$; (e) such a pair is carried by $\theta$ to a pull-back: whenever $g \in \mathrm{GL}_2(\mathbb{Q}_r)$ has matrix $E(e)$ and $t$, $t'$ are admissible for $\psi$ and $\psi\circ\mathrm{Frob}^{m'}$ respectively with $t'.X = t.X$ and the identity of (d), then `DeligneDatum.IsPullback` along $g$ holds between $\theta(\eta\,t)$ and $\theta(\eta\,t')$; (f) existence of $\Pi$-translates: for admissible $t$ there is $t'$ admissible for $\psi\circ\mathrm{Frob}$ with $t'.X.F = t.X.F$, $t'.X.\varpi = t.X.\varpi$, $t'.X.\mathrm{act}\,a = t.X.\mathrm{act}(\mathrm{Frob}\,a)$, and, for some $c$, the analogous identity with $X_i\mapsto X_i^{r}$ on the left and the reduction of $\Phi.\varpi$ on the right; (g) such a $\Pi$-translate pair has $\theta\,B\,(\psi\circ\mathrm{Frob})(\eta\,t') = \theta\,B\,\psi(\eta\,t)$.
--
--   **Conclusion.** Under these hypotheses there exist a ring homomorphism $E_0$ from the centralizer of $\{\Phi.\mathrm{actEnd}\,a\}\cup\{\Phi.\mathrm{varpiEnd}\}$ to $M_2(\mathbb{Q}_r)$, an assertion that $E_0$ is injective and that for some $m$ every $A \in M_2(\mathbb{Z}_r)$ satisfies $r^m A = E_0(e)$ for some $e$ while $r^m E_0(e)$ is integral for every $e$, and a family of maps $e_B$, defined for every Noetherian $\mathbb{Z}_r$-algebra $B$ in which the image of $r$ is nilpotent, from the $B$-points of `ModuliPackage.G ℤ_[r] M` (points $x$ carrying a $\mathbb{Z}_r$-algebra map $x.\psi : W(k)\to B$, a nilpotence witness, and a point of $M$ over $x.\psi$) to the $B$-points of the product functor `AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] r)`, whose $B$-points are pairs consisting of a $\mathbb{Z}_r$-algebra map $W(k)\to B$ and a Deligne datum over $B$ at $\pi = r$, such that:
--
--   1. $e$ is natural: for Noetherian $\mathbb{Z}_r$-algebras $B, B'$ with $r$ nilpotent and a $\mathbb{Z}_r$-algebra map $\varphi : B\to B'$, $e_{B'}$ of the image of $x$ equals the image under the product functor of $e_B(x)$;
--
--   2. each $e_B$ is bijective;
--
--   3. the first component of $e_B(x)$ is $x.\psi$;
--
--   4. for every $g \in \mathrm{GL}_2(\mathbb{Q}_r)$ and points $x, x'$, the relation `ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x'` — namely the existence of $e$ in the centralizer and of $k, m' \in \mathbb{N}$ with $E_0(e) = r^{k} g^{-1}$, with the kernel of $e$ of degree $r^{2m'}$, with $x'.\psi = x.\psi\circ Fr^{\,m'-2k}$, and with the points of $M$ underlying $x$ and $x'$ admitting, over a finite Zariski cover of $B$ by localisations, admissible rigidified lifts related by `Rigidified.IsTranslate` with parameters $k, m'$ — holds if and only if `OmegaNr.IsTwistedAct r (WittVector r k) Fr vdet B g (e_B x) (e_B x')` holds, that is, the first component of $e_B(x')$ is the first component of $e_B(x)$ precomposed with $Fr^{-vdet(g)}$ and the second components are related by `DeligneDatum.IsPullback` along $g^{-1}$;
--
--   5. if $x, x'$ satisfy `ModuliPackage.G.IsPiTranslate ι Φ η Fr` (namely $x'.\psi = x.\psi\circ Fr$, with the underlying points of $M$ admitting, Zariski-locally, admissible rigidified lifts related by `Rigidified.IsPiTranslate`), then $e_B(x')$ is the pair consisting of the first component of $e_B(x)$ precomposed with $Fr$ and the unchanged second component of $e_B(x)$;
--
--   6. for every Noetherian $\mathbb{Z}_r$-algebra $B$ and every point $x$ of `ModuliPackage.G ℤ_[r] M` over $B$ there exists $x'$ with `ModuliPackage.G.IsPiTranslate ι Φ η Fr x x'` (this last clause carries no separate nilpotence hypothesis, the nilpotence of $r$ being part of the point $x$).
--
--   This is the equivariant form of Drinfeld's representability theorem in the Čerednik–Drinfeld uniformisation: the moduli functor of special formal $\mathcal{O}_D$-modules of height $4$, bundled with its $W(k)$-leg, is identified with the product of the functor corepresented by $W(k)$ and Deligne's formal model of the $r$-adic upper half plane, compatibly with the $\mathrm{GL}_2(\mathbb{Q}_r)$-action twisted by the valuation of the determinant and with the $\Pi$-translation. It is stated over Noetherian test algebras, the hypotheses being the conclusions of the preceding representability and translation statements, and it feeds the variant [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_of_span_eq_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing.lean

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

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_G_bijective_isActBy_iff_isTwistedAct_wittVector_of_exists_forall_bijective_of_isNoetherianRing
    {r : ℕ} [Fact r.Prime] (k : Type) [Field k] [CharP k r] [IsAlgClosed k]

    [Algebra ℤ_[r] (WittVector r k)]
    (Fr : WittVector r k ≃ₐ[ℤ_[r]] WittVector r k) (hFr : ∀ x : WittVector r k, Fr x = WittVector.frobenius x)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)

    (ι : Zp2 r →+* WittVector r k)
    (Φ : FormalODModule r (WittVector r k ⧸ pIdeal r (WittVector r k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal r (WittVector r k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} r (WittVector r k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
      Rigidified r Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
          (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
          (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (r : L)),
              ∃ t : Rigidified r Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m))

    (hmaster :
    ∃ (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[r]) (r : ℤ_[r]) B)
      (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r]),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B)),
        Function.Bijective (θ B ψ hB)) ∧

      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[r] B] [Algebra ℤ_[r] B']
        (ψ : WittVector r k →+* B) (ψ' : WittVector r k →+* B')
        (hB : IsNilpotent (r : B)) (hB' : IsNilpotent (r : B')) (f : B →ₐ[ℤ_[r]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[r]) (π := (r : ℤ_[r])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x))) ∧

      (Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E e = A.map ((↑) : ℤ_[r] → ℚ_[r]))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
        ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
          FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) ∧
            t'.X = t.X ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (r ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]), (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e →
        ∀ (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ (r ^ m')) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[r]) (π := (r : ℤ_[r])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector r k →+* WittVector r k) ^ m')) hB t'))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector r k →+* B) (t : Rigidified r Φ B), t.IsAdmissible ι ψ →
          ∃ t' : Rigidified r Φ B,
            t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) ∧
            t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
            ∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (ψ : WittVector r k →+* B) (hB : IsNilpotent (r : B))
        (t t' : Rigidified r Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((r : Zp2 r) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal r B)) ^ r) =
                (t.Xbar.act ((r : Zp2 r) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector r k →+* WittVector r k)) hB t') =
            θ B ψ hB (η B ψ hB t)))
    :
    ∃
      (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[r])
      (_ : Function.Injective E₀ ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E₀ e = (r : ℚ_[r]) ^ m • A.map (algebraMap ℤ_[r] ℚ_[r])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[r], (r : ℚ_[r]) ^ m • E₀ e = A.map (algebraMap ℤ_[r] ℚ_[r])))
      (e : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B], IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r])) → (ModuliPackage.G ℤ_[r] M).obj B → (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).obj B),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (B' : Type) [CommRing B'] [IsNoetherianRing B'] [Algebra ℤ_[r] B'] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (hB' : IsNilpotent (algebraMap ℤ_[r] B' ((r : ℕ) : ℤ_[r])))
          (φ : B →ₐ[ℤ_[r]] B') (x : (ModuliPackage.G ℤ_[r] M).obj B), e B' hB' ((ModuliPackage.G ℤ_[r] M).map φ x) = (AlgFunctor.prod (AlgFunctor.corep (WittVector r k)) (Omega ℚ_[r] ((r : ℕ) : ℤ_[r]))).map φ (e B hB x)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))), Function.Bijective (e B hB)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x : (ModuliPackage.G ℤ_[r] M).obj B), (e B hB x).1 = x.ψ) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsActBy ι Φ η Fr E₀ g x x' ↔ OmegaNr.IsTwistedAct ((r : ℕ) : ℤ_[r]) (WittVector r k) Fr vdet B g (e B hB x) (e B hB x')) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (hB : IsNilpotent (algebraMap ℤ_[r] B ((r : ℕ) : ℤ_[r]))) (x x' : (ModuliPackage.G ℤ_[r] M).obj B),
          ModuliPackage.G.IsPiTranslate ι Φ η Fr x x' → e B hB x' = (frobTwist (WittVector r k) Fr 1 (e B hB x).1, (e B hB x).2)) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[r] B] (x : (ModuliPackage.G ℤ_[r] M).obj B), ∃ x' : (ModuliPackage.G ℤ_[r] M).obj B, ModuliPackage.G.IsPiTranslate ι Φ η Fr x x') := by sorry
