-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b3c6a952-ad89-56fe-8a90-5edf284935de
-- title:
--   One monodromy operator N with ρ(s)-1=t N
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal such that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$ (a rank-one condition). Let $F$ be a field extension of $L$ which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type. The reduction data consist of: fields $\bar F_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, each a curve over it and essentially of finite type, all of whose places are rational; component charts $C_i$ (a valuation subring of $F$ with a surjective residue map to $\bar F_i$ whose kernel is the maximal ideal, a set of places of $F$ over $L$, a finite set of nodes in $\bar F_i$, and a specialisation map on places) whose domains consist of rational places; pairs of annuli $An_e, An'_e$ ($e \in \mathrm{Fin}\,m$) with edge maps $\mathrm{src}, \mathrm{tgt}$, node labels $x_s(e), x_t(e)$ and weights $w(e)$, subject to: $An'_e$ and $An_e$ have the same domain and the same (nonzero) modulus and their parameters multiply to the image of that modulus; each modulus is a unit times $\pi^{w(e)}$; $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; every node of every chart is an endpoint of exactly one edge-end; every place of $F$ over $L$ lies either in exactly one chart domain and in no annulus, or in exactly one annulus domain and in no chart; for each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue has a simple zero at $Q$, lies in every place of the chart domain above $Q$ with value in the maximal ideal, and realises each element $c$ of the maximal ideal as $P.\mathrm{evalAt}\,T$ for a unique such $P$; and the genus relation $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F/L$ (pairs of ring automorphisms of $F$ and of $L$ compatible with $L \to F$) such that each $s \in S$ preserves $A$, fixes $\pi$, induces the identity on the residue field of $A$, preserves every chart domain and every annulus domain, fixes each $An_e$-parameter and each $An'_e$-parameter, preserves each chart's integers compatibly with its residue map, and commutes with each $\mathrm{placeMap}$; assume further that every automorphism of $L$ with these properties on $A$, $\pi$ and residues is the base automorphism of some $s \in S$. Let $\ell$ be a prime invertible in the residue field of $A$, assume some $s \in S$ moves an $\ell$-th root of $\pi$, and assume the rational Tate module $\mathbb{Q}_{\ell} \otimes_{\mathbb{Z}_{\ell}} T_{\ell}(\mathrm{Pic}^{0}(F/L))$ is finite-dimensional over $\mathbb{Q}_{\ell}$. Finally, let $M$ be a semistable model of these data over $A$ and $D$ a descent datum for $M$. Then there is a single $\mathbb{Q}_{\ell}$-linear endomorphism $N$ of that rational Tate module such that for every $s \in S$ there exists $t \in \mathbb{Z}_{\ell}$ with $\rho(s) - 1 = t \cdot N$, where $\rho$ is the action of semilinear automorphisms on the rational Tate module of $\mathrm{Pic}^{0}$, and $t$ is a unit whenever $s$ moves some $\ell$-th root of $\pi$.
--
--   This is the monodromy statement for the $\ell$-adic Tate module of the Jacobian of a semistably degenerating curve: the group $S$ acts through the tame character $s \mapsto t$ with a fixed nilpotent-type operator $N$ independent of $s$, as for inertia acting on the Tate module of a semistable abelian variety. The quantifier order — $N$ chosen before $s$ — is the substance; it is used to identify the kernel of $\rho - 1$ with the intersection of the kernels of the individual $\rho(s) - 1$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.exists_linearMap_forall_sub_one_eq_smul_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    ∃ N : ModularCurve.RationalTateModule ℓ (Pic0 L F) →ₗ[ℚ_[ℓ]] ModularCurve.RationalTateModule ℓ (Pic0 L F),
      ∀ s ∈ S, ∃ t : ℤ_[ℓ],
        ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1 = (t : ℚ_[ℓ]) • N ∧
        ((∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r) → IsUnit t) := by sorry
