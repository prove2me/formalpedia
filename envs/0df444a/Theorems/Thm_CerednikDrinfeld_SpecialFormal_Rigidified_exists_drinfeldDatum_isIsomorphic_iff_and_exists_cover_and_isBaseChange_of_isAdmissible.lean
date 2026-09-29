-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/a7d9e991-3dac-523a-803f-5310e9785362
-- title:
--   Drinfeld data attached to rigidified special formal 𝒪_D-modules
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : \mathbb{Z}_{p^2} \to W(k)$ (where $\mathbb{Z}_{p^2}$ denotes the Witt vectors of $\mathbb{F}_{p^2}$), and a formal $\mathcal{O}_D$-module $\Phi$ over $W(k)/pW(k)$ — a two-dimensional commutative formal group law with a $\mathbb{Z}_{p^2}$-action `act` and an endomorphism `varpi` satisfying $\varpi\circ\varpi=[p]$ and $\varpi\circ\mathrm{act}(a)=\mathrm{act}(\sigma a)\circ\varpi$ — assumed special with respect to the reduction of $\iota$ (the Lie algebra splits into the $\iota$- and $\sigma\iota$-eigenparts, both invertible) and of height $4$, i.e. the kernel algebra of $[p]$ on $\Phi$ has rank $p^4$. Then there exist: a rule $\mathcal{Q}$ assigning to every Noetherian $\mathbb{Z}_p$-algebra $B$ with a ring map $\psi : W(k)\to B$ and $p$ nilpotent in $B$, and every rigidified triple $t=(X,n,\rho)$ over $B$ ($X$ a formal $\mathcal{O}_D$-module over $B$, $n\in\mathbb{N}$, $\rho$ a pair of power series over $B/pB$), a Drinfeld datum over $B$ for $K=\mathbb{Q}_p$, $\pi=p$; and a ring homomorphism $E$ from the centraliser of $\{\mathrm{act}(a)\}\cup\{\varpi\}$ in $\mathrm{End}(\Phi.F)$ to $M_2(\mathbb{Q}_p)$, subject to six conditions. Admissibility of $t$ means: $X$ is special for $\psi\circ\iota$, $X$ has height $4$, and $\rho$ is an isogeny of formal $\mathcal{O}_D$-modules of height $4n$ from $\Phi$ base-changed along $\psi$ mod $p$ to $X$ mod $p$. (i) For admissible $t,t'$ over $B$, the Drinfeld data $\mathcal{Q}(t)$ and $\mathcal{Q}(t')$ are isomorphic if and only if $t$ and $t'$ are isomorphic in the sense of `Rigidified.IsIsomorphic` (an isomorphism of $\mathcal{O}_D$-modules matching the rigidifications after composing with a power of $[p]$). (ii) Local surjectivity: if a Drinfeld datum $Q$ over $B$ is a quadruple of a Deligne datum $d$ over $B$ (the edge-nondegeneracy and kernel conditions of `IsQuadrupleOf` hold at every point of $\operatorname{Spec} B$), then there are finitely many $f_i\in B$ generating the unit ideal such that over each localisation $L$ away from $f_i$ (Noetherian, a $\mathbb{Z}_p$-algebra over $B$, with $p$ nilpotent) there exist an admissible $t$ over $L$ and a Deligne datum $d_L$ with $\mathcal{Q}(t)$ a quadruple of $d_L$ and $d_L$ the base change of $d$ along $B\to L$. (iii) Naturality: for a $\mathbb{Z}_p$-algebra map $f:B\to B'$ with $f\circ\psi=\psi'$ and $t$ admissible over $B$, if $\mathcal{Q}(t)$ is a quadruple of $d$ and $\mathcal{Q}(t.\mathrm{map}\,f)$ a quadruple of $d'$, then $d'$ is the base change of $d$ along $f$. (iv) $E$ is injective and there is $m$ with $p^m M_2(\mathbb{Z}_p)$ contained in the image of $E$ and $p^m E(e)$ integral for every $e$. (v) Equivariance: if $e$ lies in the centraliser, its kernel algebra has rank $p^{2m'}$, $g\in \mathrm{GL}_2(\mathbb{Q}_p)$ has matrix $E(e)$, and $t$, $t'$ over $B$ are admissible for $\psi$ and for $\psi\circ\mathrm{Frob}^{m'}$ respectively, have the same underlying $\mathcal{O}_D$-module, and satisfy, for some $c$, the identity $\mathrm{act}(p^{c+n_t})\circ(\rho_{t'}\circ(X_i\mapsto X_i^{p^{m'}}))=\mathrm{act}(p^{c+n_{t'}})\circ(\rho_t\circ e)$ over $B/pB$, then any Deligne data $d,d'$ of which $\mathcal{Q}(t)$ and $\mathcal{Q}(t')$ are quadruples satisfy $d'.\mathrm{line}(M)=g$-pullback of $d.\mathrm{line}$, i.e. `DeligneDatum.IsPullback`. (vi) Likewise, if $t'$ is admissible for $\psi\circ\mathrm{Frob}$, has the same formal group law and `varpi` as $t$ while $\mathrm{act}_{t'}(a)=\mathrm{act}_t(\sigma a)$, and for some $c$ the corresponding identity with $X_i\mapsto X_i^p$ and $\Phi.\varpi$ holds, then $d'=d$.
--
--   This is Drinfeld's classification of rigidified special formal $\mathcal{O}_D$-modules over $p$-nilpotent Noetherian bases in terms of the lattice-theoretic (Drinfeld/Deligne) description of the formal upper half plane, in the form used for the Čerednik–Drinfeld uniformisation: a comparison map on objects together with injectivity on isomorphism classes, Zariski-local surjectivity, naturality in the base, the embedding of the $\mathcal{O}_D$-endomorphism ring of $\Phi$ as an order in $M_2(\mathbb{Q}_p)$, and the resulting $\mathrm{GL}_2(\mathbb{Q}_p)$- and $\varpi$-equivariances. It feeds the construction of the moduli package for the uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_drinfeldDatum_isIsomorphic_iff_and_exists_cover_and_isBaseChange_of_isAdmissible
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
(hΦ4 : Φ.HasHeight 4) :
∃ (𝒬 : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
      Rigidified p Φ B → DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
  (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p]),

  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ → t'.IsAdmissible ι ψ →
    ((𝒬 B ψ hB t).IsIsomorphic (𝒬 B ψ hB t') ↔ t.IsIsomorphic t')) ∧

  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B), Q.IsQuadrupleOf d →
    ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
      ∀ (i : Fin n) (L : Type) [CommRing L] [IsNoetherianRing L] [Algebra B L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] B L]
        [IsLocalization.Away (f i) L] (hL : IsNilpotent (p : L)),
        ∃ (t : Rigidified p Φ L) (dL : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) L),
          t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧
          (𝒬 L ((algebraMap B L).comp ψ) hL t).IsQuadrupleOf dL ∧
          DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) (IsScalarTower.toAlgHom ℤ_[p] B L) d dL) ∧

  (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
    ∀ (d : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B) (d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B'),
      (𝒬 B ψ hB t).IsQuadrupleOf d → (𝒬 B' ψ' hB' (t.map (f : B →+* B'))).IsQuadrupleOf d' →
      DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f d d') ∧

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
      ∀ (d d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
        (𝒬 B ψ hB t).IsQuadrupleOf d →
        (𝒬 B (ψ.comp ((WittVector.frobenius : WittVector p k →+* WittVector p k) ^ m')) hB t').IsQuadrupleOf d' →
        DeligneDatum.IsPullback (K := ℚ_[p]) (π := (p : ℤ_[p])) B g d d') ∧

  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B))
    (t t' : Rigidified p Φ B), t.IsAdmissible ι ψ →
      t'.IsAdmissible ι (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) →
      t'.X.F = t.X.F → t'.X.varpi = t.X.varpi → (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) →
      (∃ c : ℕ,
          (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
              (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
            (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))) →
      ∀ (d d' : DeligneDatum (K := ℚ_[p]) (p : ℤ_[p]) B),
        (𝒬 B ψ hB t).IsQuadrupleOf d →
        (𝒬 B (ψ.comp (WittVector.frobenius : WittVector p k →+* WittVector p k)) hB t').IsQuadrupleOf d' → d' = d) := by sorry
