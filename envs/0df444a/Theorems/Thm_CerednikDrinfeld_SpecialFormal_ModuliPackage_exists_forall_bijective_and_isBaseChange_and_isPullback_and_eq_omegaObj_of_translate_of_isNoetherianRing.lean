-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_bijective_and_isBaseChange_and_isPullback_and_eq_omegaObj_of_translate_of_isNoetherianRing
-- name    : CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_and_eq_omegaObj_of_translate_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:17.868596+00:00
-- url     : https://prove2.me/theorems/49f166d9-13be-50d7-885e-c72f16499a89
-- title:
--   Drinfeld representability for rigidified special formal mathcal O_D-modules
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota\colon \mathbb Z_{p^2}=W(\mathbb F_{p^2})\to W(k)$, and a formal $\mathcal O_D$-module $\Phi$ over $W(k)/pW(k)$, i.e. a commutative two-dimensional formal group law carrying an action of $\mathbb Z_{p^2}$ and an endomorphism $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\mathrm{Fr}(a)]\circ\varpi$; assume $\Phi$ is special for $\iota$ composed with reduction (its Lie algebra splits as the direct sum of the two invertible eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$) and of height $4$ (the kernel algebra of $[p]$ is finite projective with all fibre dimensions $p^4$). Let $M$ be a `ModuliPackage` over $W(k)$ — a functor $B,\psi\colon W(k)\to B,\ p$ nilpotent in $B$, $\mapsto M(B,\psi)$ with functorial transition maps — which is a Zariski sheaf, and let $\eta$ assign to every rigidified triple $t=(X,n,\rho)$ over such $B$ an element $\eta_{B,\psi}(t)\in M(B,\psi)$, subject, over Noetherian $B$, to: (i) for admissible $t,t'$ (meaning $X$ special for $\psi\circ\iota$ of height $4$ and $\rho$ an $\mathcal O_D$-linear isogeny of height $4n$ from $\Phi\otimes B/pB$ to $X\otimes B/pB$), $\eta(t)=\eta(t')$ if and only if $t$ and $t'$ are isomorphic in the rigidified sense; (ii) compatibility of $\eta$ with arbitrary $\psi$-compatible ring maps $f\colon B\to B'$ applied to admissible $t$; (iii) every element of $M(B,\psi)$ becomes, over the members of some finite cover of $B$ by localisations away from elements generating the unit ideal, the image under $\eta$ of an admissible triple. The conclusion asserts the existence of maps $\theta_{B,\psi}\colon M(B,\psi)\to \mathrm{OmegaObj}$, for $B$ a Noetherian $\mathbb Z_p$-algebra with $p$ nilpotent, into the set of Deligne data over $B$ for $(\mathbb Z_p,\mathbb Q_p,p)$ (a $B$-submodule of $B\otimes L$ for every full lattice $L\subset\mathbb Q_p^2$, with invertible quotient, monotone under inclusions of lattices, equivariant for scalar homotheties, and non-degenerate at every prime ideal of $B$), together with a ring homomorphism $E$ from the centraliser of $\{\,[a]:a\in\mathbb Z_{p^2}\}\cup\{\varpi\}$ in the endomorphism ring of the formal group law of $\Phi$ to $M_2(\mathbb Q_p)$, such that: each $\theta_{B,\psi}$ is bijective; $\theta$ carries the transition maps of $M$ along $\mathbb Z_p$-algebra maps $f$ to the base-change relation for Deligne data (the lines of the target datum are the $B'$-spans of the images of the lines of the source); $E$ is injective and there is an $m$ with $p^m M_2(\mathbb Z_p)\subseteq E(\cdot)$ attained and $p^m E(e)$ integral for every $e$; for $e$ in that centraliser whose underlying pair of power series has kernel of degree $p^{2m'}$ and for $g\in GL_2(\mathbb Q_p)$ with $g=E(e)$, if $t$ is admissible for $\psi$, $t'$ is admissible for $\psi\circ\mathrm{Fr}^{m'}$, $t'.X=t.X$ and the rigidifications satisfy, for some $c$, the identity equating $[p^{c+n}]\circ(t'.\rho$ precomposed with $X_i\mapsto X_i^{p^{m'}})$ with $[p^{c+n'}]\circ(t.\rho$ precomposed with the reduction of $e)$, then $\theta(\eta(t'))$ is the pullback of $\theta(\eta(t))$ along $g$ (its line at $L$ is the preimage of the line at $g\cdot L$); and, finally, if $t$ is admissible for $\psi$, $t'$ admissible for $\psi\circ\mathrm{Fr}$ with the same formal group law and the same $\varpi$ as $t$ and $t'.X$'s action given by $a\mapsto t.X$-action of $\mathrm{Fr}(a)$, and if for some $c$ the analogous identity with $p$-th power substitution on $t'.\rho$ and the reduction of $\Phi$'s $\varpi$ holds, then $\theta(\eta(t'))=\theta(\eta(t))$.
--
--   This is Drinfeld's representability theorem for the moduli problem of rigidified special formal $\mathcal O_D$-modules of height $4$, in the form in which the moduli package $M$ is represented by the functor of Deligne data for $(\mathbb Z_p,\mathbb Q_p,p)$ — the formal model $\widehat\Omega$ of the $p$-adic upper half plane — together with the identification of the $\mathcal O_D$-linear endomorphism ring of $\Phi$ with an order in $M_2(\mathbb Q_p)$ and the two equivariance identities describing the $GL_2(\mathbb Q_p)$-action twisted by powers of Frobenius on $W(k)$. The maps $\eta$ from rigidified triples to $M$ are taken as given data here; the result feeds the Cerednik–Drinfeld uniformisation step, being cited by [`CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing`](thm.html#CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_omegaObj_of_isZariskiSheaf_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_ModuliPackage_exists_forall_bijective_and_isBaseChange_and_isPullback_and_eq_omegaObj_of_translate_of_isNoetherianRing.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.ModuliPackage.exists_forall_bijective_and_isBaseChange_and_isPullback_and_eq_omegaObj_of_translate_of_isNoetherianRing
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (M : ModuliPackage.{0, 0} p (WittVector p k)) (hM : M.IsZariskiSheaf)
    (η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → M.obj B ψ hB)
    (hη : (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
          (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
          (η B ψ hB t = η B ψ hB t' ↔ t.IsIsomorphic t')) ∧
      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
          (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →+* B')
          (hf : f.comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
          η B' ψ' hB' (t.map f) = M.map hB hB' f hf (η B ψ hB t)) ∧
      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)) (m : M.obj B ψ hB),
          ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
            ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [IsLocalization.Away (f i) L]
              (hL : IsNilpotent (p : L)),
              ∃ t : Rigidified p Φ L, t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
                η L ((algebraMap B L).comp ψ) hL t =
                  M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m)) :
    ∃ (θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
        M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B)
      (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]),

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
        Function.Bijective (θ B ψ hB)) ∧

      (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
        (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
        (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
        (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
        DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x)
          (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x))) ∧

      (Function.Injective E ∧
        ∃ m : ℕ,
          (∀ A : Matrix (Fin 2) (Fin 2) ℤ_[p], ∃ e, E e = (p : ℚ_[p]) ^ m • A.map ((↑) : ℤ_[p] → ℚ_[p])) ∧
          (∀ e, ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p], (p : ℚ_[p]) ^ m • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
        (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (m' : ℕ),
        FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')) →
        ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p]), (g : Matrix (Fin 2) (Fin 2) ℚ_[p]) = E e →
        ∀ (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) →
          t'.X = t.X →
          (∃ c : ℕ,
              (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ (p ^ m')) =
                (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
                  (t.ρ.comp (Series.map (residueMap ψ) (e : MvFormalGroup.End Φ.F).toPowerSeries))) →
          DeligneDatum.IsPullback (K := ℚ_[p]) (π := (p : ℤ_[p])) B g (θ B ψ hB (η B ψ hB t))
            (θ B (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) hB
              (η B (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) hB t'))) ∧

      (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
        (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ →
          t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) →
          t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
          (∃ c : ℕ,
              (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
                  (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
                (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
          θ B (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hB
              (η B (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hB t') =
            θ B ψ hB (η B ψ hB t)) := by sorry
