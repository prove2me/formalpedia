-- Prove2me | Theorems.Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
-- name    : CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/c6bce862-2d81-57b5-839d-14685c3ffb44
-- title:
--   Stalks of the η-lattice data of an admissible rigidified module
-- statement:
--   Fix a prime $p$, an algebraically closed field $k$ of characteristic $p$, a ring homomorphism $\iota : W(\mathbb{F}_{p^2}) \to W(k)$, and a formal $\mathcal{O}_D$-module $\Phi$ of dimension $2$ over $W(k)/pW(k)$, written with respect to $\bar\jmath = \iota$ followed by reduction mod $p$. Assume: $\Phi$ is special, i.e. its Lie algebra is the direct sum of the eigen-submodules $\mathrm{lieZero}$ and $\mathrm{lieOne}$ for the $W(\mathbb{F}_{p^2})$-action (via $\bar\jmath$ and via $\bar\jmath\circ\sigma$ respectively), both invertible; $\Phi$ has height $4$; $\mathrm{lieZero}$ is killed by the linear part of $\varpi$; the degree-$0$ and degree-$1$ graded pieces of the Cartier module of $\Phi$ (the eigenspaces for the Teichmüller action with eigenvalue $\bar\jmath(c)$, resp. $\bar\jmath(c)^p$) are complementary, with complementation witness $h_{c\Phi}$, yielding the graded Cartier module data $D_\Phi$; $r_\Phi : \mathbb{Z}_p^2 \to D_\Phi.\mathrm{NMod}$ is additive; a canonical $L$-map for $D_\Phi$ exists; and for every canonical $L$-map $L$, $r_\Phi$ carries $\mathbb{Z}_p^2$ bijectively onto the degree-$0$ part $\mathrm{etaPiece}\,L\,0$. Let $B$ be a Noetherian commutative $\mathbb{Z}_p$-algebra in which $p$ is nilpotent, $\psi : W(k) \to B$ a ring homomorphism, and $t = (X,n,\rho)$ a rigidified object over $B$ which is admissible for $(\iota,\psi)$: $X$ is special for $\psi\circ\iota$, has height $4$, and $\rho$ is an isogeny of height $4n$ from the reduction of $\Phi$ to the reduction of $X$. Then there exist maps $N_0, N_1$ from $\operatorname{Spec} B$ to the $\mathbb{Z}_p$-submodules of $\mathbb{Q}_p^2$ such that, for $i \in \{0,1\}$, a vector $v$ lies in $N_i(x)$ if and only if there are $f \notin x$, complementation data $h_c$, $h_{cb}$, $h_{c\Phi f}$ for the graded pieces of the Cartier modules of $X$ over $B_f$, of its reduction mod $p$, and of the base change of $\Phi$ to $B_f/p$, a canonical $L$-map $L$ for the graded data of $X$ over $B_f$, and an element $z$ with $\mathrm{IsEtaSection}$ holding for $(L,i,z,v)$ — that is, $z$ lies in $\mathrm{etaPiece}\,L\,i$ and the pair $(\text{image of } \varpi^i z \text{ in the reduced } N\text{-module},\; p^i v)$ satisfies the relation $\mathrm{LatticeRel}$ at level $n$ for the rigidification obtained from $r_\Phi$ by base change along $\rho$; and such that each $N_i(x)$ is a full lattice (finitely generated and spanning $\mathbb{Q}_p^2$), $N_0(x) \le N_1(x)$, $p\,N_1(x) \subseteq N_0(x)$, each set $\{x : v \in N_i(x)\}$ is open, $N_0$ is locally constant on the locus where $\varpi(\mathrm{lieZero}) \subseteq x\cdot\mathrm{lieOne}$ and $N_1$ on the locus where $\varpi(\mathrm{lieOne}) \subseteq x\cdot\mathrm{lieZero}$, and on those two loci $N_0(x)$ has determinant index $0$ and $N_1(x)$ determinant index $-1$ (i.e. $N_i(x) = g\cdot\mathbb{Z}_p^2$ for some $g \in \mathrm{GL}_2(\mathbb{Q}_p)$ with $\det g$ a unit times $p^e$ for the given $e$).
--
--   This assembles, at every point of $\operatorname{Spec} B$, the pair of $p$-adic lattices attached to an admissible rigidified special formal $\mathcal{O}_D$-module by Drinfeld's period construction, together with all the properties required of a Deligne/Drinfeld datum: fullness, the chain $pN_1 \subseteq N_0 \subseteq N_1$, openness of the membership loci, local constancy on the two strata cut out by the $\varpi$-action on the graded Lie algebra, and the determinant indices $0$ and $-1$. It is the input to the construction of the Cartier quadruple associated with an admissible rigidified module, and is obtained by combining the separate existence, fullness, local-constancy and determinant-index statements for the two indices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_SpecialFormal_Rigidified_exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_submodule_mem_iff_isEtaSection_and_isFullLattice_of_isAdmissible_of_lieZero_le_ker_wittVector
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (h0Φ : Φ.lieZero (Rigidified.jbar ι) ≤ LinearMap.ker Φ.lieVarpi)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ) :
    ∃ (N₀ N₁ : PrimeSpectrum B → Submodule ℤ_[p] (Fin 2 → ℚ_[p])),
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₀ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 0 z v) ∧
      (∀ (x : PrimeSpectrum B) (v : Fin 2 → ℚ_[p]), v ∈ N₁ x ↔
          ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
            (hcb : t.IsGradedSbar ι ψ (Rigidified.awayHom f)) (hcΦf : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f))
            (L : _) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
            ∃ z, t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f) hc hcb hcΦf L hL 1 z v) ∧
      (∀ x, LT.LatticeTree.IsFullLattice (N₀ x)) ∧ (∀ x, LT.LatticeTree.IsFullLattice (N₁ x)) ∧
      (∀ x, N₀ x ≤ N₁ x) ∧
      (∀ x, ∀ v ∈ N₁ x, algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v ∈ N₀ x) ∧
      (∀ v : Fin 2 → ℚ_[p], IsOpen {x : PrimeSpectrum B | v ∈ N₀ x}) ∧
      (∀ v : Fin 2 → ℚ_[p], IsOpen {x : PrimeSpectrum B | v ∈ N₁ x}) ∧

      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
          ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieOne (structureMap ι ψ) →
              N₀ y = N₀ x) ∧
      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
          ∃ U : Set (PrimeSpectrum B), IsOpen U ∧ x ∈ U ∧
            ∀ y ∈ U, Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ y.asIdeal • t.X.lieZero (structureMap ι ψ) →
              N₁ y = N₁ x) ∧

      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieZero (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieOne (structureMap ι ψ) →
          FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₀ x) 0) ∧
      (∀ x : PrimeSpectrum B,
          Submodule.map t.X.lieVarpi (t.X.lieOne (structureMap ι ψ)) ≤ x.asIdeal • t.X.lieZero (structureMap ι ψ) →
          FormalOmega.HasDetIndex (K := ℚ_[p]) (p : ℤ_[p]) (N₁ x) (-1)) := by sorry
