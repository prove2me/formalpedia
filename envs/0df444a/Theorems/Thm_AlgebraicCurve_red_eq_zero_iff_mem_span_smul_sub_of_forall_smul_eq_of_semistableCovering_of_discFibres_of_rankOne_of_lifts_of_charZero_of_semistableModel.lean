-- Prove2me | Theorems.Thm_AlgebraicCurve_red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/1daaa2bb-34ce-5f98-873d-cb25e38f5c38
-- title:
--   Vanishing of chart reduction on S-invariants equals augmentation span
-- statement:
--   Fix an algebraically closed field $L$ of characteristic zero, a valuation subring $A \subseteq L$, and $\pi \neq 0$ in the maximal ideal of $A$, with $A$ of rank one in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field over $L$ which is a curve over $L$ (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$. Over the residue field $\kappa$ of $A$ let $\bar F_{0},\dots,\bar F_{n-1}$ be fields, all of whose places are rational, each a curve over $\kappa$ and essentially of finite type over $\kappa$; let $C_{i}$ be component charts of $F$ along $A$ with residue field $\bar F_{i}$ (a valuation subring `integers` of $F$ with surjective residue map onto $\bar F_{i}$ whose kernel is the maximal ideal, a domain of places of $F$, a finite set of nodes in $\bar F_{i}$, and a place map), all places in the chart domains being rational. Let $An_{e}, An'_{e}$ ($e \in \mathrm{Fin}\ m$) be annuli with $\mathrm{src}(e), \mathrm{tgt}(e)$, node places $x_{s}(e), x_{t}(e)$ and widths $w(e)$, subject to: $An'_{e}$ has the same domain and the same modulus as $An_{e}$, this modulus is nonzero in $L$ and is the product of the two parameters, the modulus equals a unit times $\pi^{w(e)}$, and $An_{e}$, resp. $An'_{e}$, is attached to $C_{\mathrm{src}(e)}$ at $x_{s}(e)$, resp. to $C_{\mathrm{tgt}(e)}$ at $x_{t}(e)$ (the node lies in the chart's node set, the annulus parameter is integral with residue of order one at the node, and evaluations of chart functions with nonzero residue and trivial order on the annulus are units after the correcting power of the parameter). Further hypotheses: every node of every chart is an end of some annulus and of exactly one end among the $2m$ ends; every place of $F$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; over each non-node place $Q$ of $\bar F_{i}$ the fibre of the place map is a disc, i.e. there is an integral $T$ with nonzero residue of order one at $Q$, integral with value in the maximal ideal at each place of the domain above $Q$, and taking each value in the maximal ideal exactly once there; and the genus identity $g(F) + n = \sum_{i} g(\bar F_{i}) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F$ over $L$ (pairs of ring automorphisms of $F$ and of $L$ compatible with the structure map) such that each $s \in S$ stabilises $A$, fixes $\pi$, induces the identity on the residue field, preserves each chart domain and each annulus domain, fixes every $An_{e}$- and $An'_{e}$-parameter, preserves chart integers compatibly with the residue maps, and commutes with the place maps; assume moreover that every ring automorphism of $L$ stabilising $A$, fixing $\pi$ and inducing the identity on the residue field is the base automorphism of some $s \in S$. Let $\ell$ be a prime, invertible in $\kappa$, such that some $s \in S$ moves some $\ell$-th root of $\pi$ in $L$. Assume the rational $\ell$-adic Tate module $V = \mathbb{Q}_{\ell} \otimes_{\mathbb{Z}_{\ell}} T_{\ell}(\mathrm{Pic}^{0}(F/L))$ is finite dimensional, and let $\mathrm{red}$ be a $\mathbb{Q}_{\ell}$-linear map from the subspace of vectors fixed by $\rho(s)$ for all $s \in S$ to $\prod_{i} \mathbb{Q}_{\ell} \otimes T_{\ell}(\mathrm{Pic}^{0}(\bar F_{i}/\kappa))$, compatible with divisors in the following sense: whenever such a fixed vector $v$ is $1 \otimes x$ for an integral Tate vector $x$, whenever a degree-zero divisor $D$ represents the $k$-th component of $x$ in $\mathrm{Pic}^{0}$, and whenever $D = \sum_{i} D_{i}$ with each $D_{i}$ of degree zero and supported in the domain of $C_{i}$, then for each $i$ the $i$-th component of $\mathrm{red}\,v$ is $1 \otimes y$ for an integral Tate vector $y$ whose $k$-th component is the class of any degree-zero divisor equal to the push-forward of $D_{i}$ along the place map of $C_{i}$. Assume finally that $\mathrm{Pic}^{0}(\bar F_{i}/\kappa)$ has exactly $\ell^{2 g(\bar F_{i}) k}$ points of order dividing $\ell^{k}$ for all $i, k$, and fix a semistable model $M$ of these data over $A$ together with a descent $D$ of $M$. Then for every $S$-fixed vector $v$, one has $\mathrm{red}\, v = 0$ if and only if $v$ lies in the $\mathbb{Q}_{\ell}$-span of the set of all differences $\rho(s)w - w$ with $s \in S$ and $w \in V$.
--
--   This is the monodromy description of the kernel of reduction on the inertia invariants of the $\ell$-adic Tate module of a semistable curve: the invariant classes dying under reduction to the components of the special fibre are exactly those in the augmentation span of the inertia action. It is used by the three [`ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa`](thm.html#ModularCurve.FullLevel.exists_linearMap_tateProd_comp_baseChange_eq_and_eq_zero_of_semistableCovering_of_semistableModel_of_inertiaIgusa) statements, where the component charts are the Igusa components of a modular curve at the relevant residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.red_eq_zero_iff_mem_span_smul_sub_of_forall_smul_eq_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    (hcount : ∀ (i : Fin n) (k : ℕ),
      Nat.card (Pic0.torsion (IsLocalRing.ResidueField A) (Fbar i) (ℓ ^ k)) =
        ℓ ^ (2 * genusFF (IsLocalRing.ResidueField A) (Fbar i) * k))
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    :
    ∀ v : ↥(⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1)),
      (red v = 0 ↔ (v : ModularCurve.RationalTateModule ℓ (Pic0 L F)) ∈ Submodule.span ℚ_[ℓ] {u | ∃ s ∈ S, ∃ w,
        u = ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s w - w}) := by sorry
