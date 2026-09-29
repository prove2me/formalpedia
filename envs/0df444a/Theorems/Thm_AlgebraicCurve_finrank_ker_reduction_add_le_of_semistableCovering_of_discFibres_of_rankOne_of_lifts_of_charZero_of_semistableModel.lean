-- Prove2me | Theorems.Thm_AlgebraicCurve_finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/42e9e7bd-720e-57ed-9b4e-fb44dbb1dbc1
-- title:
--   Toric bound for the kernel of chartwise reduction
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; assume $A$ has rank one in the form that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F/L$ be a field extension which is a curve over $L$ (principal divisors exist, all residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank $1$ over $F$) and essentially of finite type. Combinatorial data are given: $n$ fields $\bar F_i$ over the residue field $k = A/\mathfrak m$, each with all places rational and itself a curve over $k$; component charts $C_i$ (a valuation subring of $F$ with residue map onto $\bar F_i$, a set of places of $F$, a finset of nodes among the places of $\bar F_i$, and a place map, subject to the chart axioms), with all places in chart domains rational; and for $e < m$ annuli $An_e$, $An'_e$ with edge maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, node places $x^{s}_e, x^{t}_e$ and weights $w_e$. The hypotheses require: $An'_e$ and $An_e$ have the same domain and the same nonzero modulus, and the product of their parameters is the image of that modulus; each modulus is a unit times $\pi^{w_e}$; $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{s}_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{t}_e$; every node of every chart is an endpoint of some edge, and the assignment of the $2m$ endpoints to nodes is injective; every place of $F$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; over each non-node place $Q$ of $\bar F_i$ the fibre of the place map is a disc, witnessed by an integral element $T$ of $C_i$ whose residue has $\mathrm{ord}_Q = 1$, which is integral with value in $\mathfrak m$ at every place above $Q$ and takes each value in $\mathfrak m$ exactly once there; and the genus identity $g(F) + n = \sum_i g(\bar F_i) + m + 1$. Further, $S$ is a set of semilinear automorphisms of $F$ (pairs of ring automorphisms of $F$ and of $L$ compatible over $L$) each of which preserves $A$, fixes $\pi$, induces the identity on $k$, preserves every chart domain and every annulus domain, fixes all parameters of the $An_e$ and of the $An'_e$, preserves each $C_i$'s integers with unchanged residue, and commutes with each place map; every automorphism of $L$ preserving $A$, fixing $\pi$ and trivial on $k$ is realised by some $s \in S$; $\ell$ is a prime invertible in $k$, and some $s \in S$ moves some $\ell$-th root $r$ of $\pi$. Assume the rational Tate module $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F))$ is finite-dimensional, and let $\mathrm{red}$ be a $\mathbb{Q}_\ell$-linear map from the $S$-invariants $\bigcap_{s \in S} \ker(\rho_\ell(s) - 1)$ to $\prod_i \mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(\bar F_i))$, subject to the pinning hypothesis: whenever an invariant $v$ equals $1 \otimes x$ for $x$ in the integral Tate module, and at level $k$ the class $\mathrm{proj}_k(x)$ is represented by a degree-zero divisor $D = \sum_i D_i$ with each $D_i$ supported in the domain of $C_i$ and of degree $0$, then for each $i$ one has $\mathrm{red}(v)_i = 1 \otimes y$ with $\mathrm{proj}_k(y)$ the class of the push-forward of $D_i$ along the place map of $C_i$. Finally $M$ is a semistable model of these data over $A$ and $D$ a descent datum for $M$. The conclusion is $\dim_{\mathbb{Q}_\ell} \ker(\mathrm{red}) + n \le m + 1$.
--
--   This is the bound on the toric part: the invariants annihilated by the chartwise reduction have dimension at most the first Betti number $m - n + 1$ of the incidence graph of the semistable covering, the inequality being stated additively to avoid truncated subtraction on $\mathbb{N}$. It is obtained by combining the representation of invariant classes by chart-supported divisors of chartwise degree zero with a counting bound for finite-level representatives, and is used in the identification of the vanishing-cycle part of the $\ell$-adic representation attached to $\mathrm{Pic}^0(F)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.finrank_ker_reduction_add_le_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    (red : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)) →ₗ[ℚ_[ℓ]]
      ∀ i, ModularCurve.RationalTateModule ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)))
    (hred : ∀ (v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)))
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
              TateModule.proj ℓ (Pic0 (IsLocalRing.ResidueField A) (Fbar i)) k y = Pic0.mk E)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    Module.finrank ℚ_[ℓ] ↥(LinearMap.ker red) + n ≤ m + 1 := by sorry
