-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/8b8f31e1-ae72-54f7-b455-02d5b8117b35
-- title:
--   Existence of chartwise reduction on inertia invariants
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A \subseteq L$ a valuation subring and $\pi \in A$ a nonzero element of the maximal ideal, and assume $A$ has rank one in the form: for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ satisfies $v(y^{n}) \le v(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ (finitely supported principal divisors of degree zero, finite residue extensions, and $\Omega_{F/L}$ free of rank one) and essentially of finite type. The geometry of a semistable covering is given by: fields $\bar F_i$ ($i < n$) over the residue field of $A$, all of whose places are rational, component charts $C_i$ on $F$ with residue curve $\bar F_i$, all places in the chart domains being rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e < m$) with source and target indices $\mathrm{src}\,e, \mathrm{tgt}\,e$ and nodes $x_s(e), x_t(e)$; weights $w_e$; hypotheses that $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same nonzero modulus and their parameters multiply to that modulus, that each modulus is a unit times $\pi^{w_e}$, that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$, that every node of every chart is an endpoint of exactly one annulus end, that every place of $F/L$ lies in exactly one chart domain and in no annulus domain or else in exactly one annulus domain and in no chart domain, that over every non-node place $Q$ of $\bar F_i$ there is a chart function $T$ with nonzero residue having a simple zero at $Q$, with $T$ in the valuation ring of each place of the chart domain above $Q$ and $\mathrm{ev}_P(T)$ in the maximal ideal of $A$ there, and with a unique place $P$ of the chart domain over $Q$ realising each prescribed value $\mathrm{ev}_P(T) = c$ in the maximal ideal, and finally the genus relation $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$. Let $S$ be a set of automorphisms of $F$ semilinear over automorphisms of $L$ such that each $s \in S$ has base automorphism stabilising $A$, fixing $\pi$ and inducing the identity on the residue field of $A$, and such that $s$ preserves every chart domain and annulus domain, fixes both annulus parameters, preserves each chart's ring of integers and induces the identity on each residue field $\bar F_i$, and commutes with each place map; assume moreover that every automorphism of $L$ stabilising $A$, fixing $\pi$ and trivial on the residue field is the base automorphism of some element of $S$. Let $\ell$ be a prime which is a unit in the residue field of $A$, assume some $s \in S$ moves an $\ell$-th root of $\pi$, and assume the rational Tate module $\mathbb{Q}_{\ell} \otimes_{\mathbb{Z}_{\ell}} T_{\ell}\,\mathrm{Pic}^{0}(F/L)$ is finite-dimensional, each $\bar F_i$ being a curve over the residue field of $A$ and essentially of finite type over it. Given in addition a semistable model $M$ of the covering data and a descent datum $D$ for $M$, the conclusion asserts the existence of a $\mathbb{Q}_{\ell}$-linear map $\mathrm{red}$ from $\bigcap_{s \in S} \ker(\rho_{\ell}(s) - 1)$, the $S$-invariants of the rational Tate module of $\mathrm{Pic}^{0}(F/L)$, to $\prod_i \mathbb{Q}_{\ell} \otimes_{\mathbb{Z}_{\ell}} T_{\ell}\,\mathrm{Pic}^{0}(\bar F_i)$, with the following specialisation property: whenever $v$ is an invariant vector of the shape $1 \otimes x$ for $x \in T_{\ell}\,\mathrm{Pic}^{0}(F/L)$, whenever $k \in \mathbb{N}$ and a degree-zero divisor $D$ on $F/L$ represents the $k$-th component of $x$ in $\mathrm{Pic}^{0}$, and whenever $D = \sum_i D_i$ with each $D_i$ supported in the domain of $C_i$ and of degree zero, then for each $i$ there is $y \in T_{\ell}\,\mathrm{Pic}^{0}(\bar F_i)$ with $\mathrm{red}\,v\,i = 1 \otimes y$ such that every degree-zero divisor $E$ on $\bar F_i$ equal to the pushforward of $D_i$ along the place map of $C_i$ represents the $k$-th component of $y$ in $\mathrm{Pic}^{0}(\bar F_i)$.
--
--   This is the existence of the chartwise specialisation (reduction) map from the inertia invariants of the $\ell$-adic Tate module of the Jacobian of a semistably covered curve to the Tate modules of the Jacobians of the components of the reduction, in the arithmetic form where the covering is accompanied by a semistable model over $A$ together with a descent datum. It is the input to the vanishing-cycles estimate for an edge joining two distinct components and to the computation of the inertia action on the Tate module of $J$ at full level for the Igusa-type reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_linearMap_rationalTateModule_reduction_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∃ red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
    ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
      (x : TateModule ℓ (Pic0 L F)), (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x →
      ∀ (k : ℕ) (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
      Pic0.mk ⟨D, hD⟩ = TateModule.proj ℓ (Pic0 L F) k x →
      ∀ Di : Fin n → Divisor L F, D = ∑ i, Di i → (∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom) →
        (∀ i, Divisor.degree (Di i) = 0) →
        ∀ i, ∃ y : TateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)),
          red v i = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] y ∧
          ∀ E : Divisor.degZero (K := IsLocalRing.ResidueField A) (F := Fbar i),
            (E : Divisor (IsLocalRing.ResidueField A) (Fbar i)) =
                Finsupp.mapDomain (C i).placeMap (Di i) →
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E := by sorry
