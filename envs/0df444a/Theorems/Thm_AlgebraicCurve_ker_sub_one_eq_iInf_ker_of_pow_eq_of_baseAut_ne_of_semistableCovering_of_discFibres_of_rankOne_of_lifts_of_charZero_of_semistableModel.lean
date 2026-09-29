-- Prove2me | Theorems.Thm_AlgebraicCurve_ker_sub_one_eq_iInf_ker_of_pow_eq_of_baseAut_ne_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.ker_sub_one_eq_iInf_ker_of_pow_eq_of_baseAut_ne_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/e977e684-4213-51ad-9a07-572b6c05417a
-- title:
--   One S-element moving an ℓ-th root of π cuts out all invariants
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; the hypothesis `hrk` asks that for every nonzero $x \in L$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$ (rank one). Let $F/L$ be a field extension which is a curve over $L$ in the project's sense (principal divisors of all nonzero functions exist with degree zero, all place residue fields finite over $L$, and $\Omega_{F/L}$ free of rank one over $F$) and essentially of finite type, and let $\mathrm{Fbar} : \mathrm{Fin}\,n \to \mathrm{Type}$ be field extensions of the residue field of $A$, each again a curve and essentially of finite type, with all places rational. The combinatorial and geometric data are: component charts $C\,i$ (a valuation subring of $F$ with surjective residue map onto $\mathrm{Fbar}\,i$ whose kernel is the maximal ideal, a domain of places of $F/L$ all of which are rational, a finite set of nodes, and a place map), annuli $\mathrm{An}\,e, \mathrm{An}'\,e$ with sources and targets $\mathrm{src}, \mathrm{tgt}$ and node places $xs, xt$, weights $w$, and the hypotheses, summarised here, that the two annuli of an edge share domain and nonzero modulus and have parameters with product the modulus (`hpair`), that each modulus is a unit times $\pi^{w(e)}$ (`hw`), that the annuli are attached to the charts at the named nodes (`hatt`), that the $2m$ half-edges hit every node of every chart exactly once (`hnodes`), that every place of $F/L$ lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain (`hcover`), that each non-node place $Q$ of $\mathrm{Fbar}\,i$ carries a disc parameter $T$ in the chart integers whose residue has order $1$ at $Q$ and which identifies the places above $Q$ with the maximal ideal of $A$ (`hdisc`), and the genus relation $g(F/L) + n = \sum_i g(\mathrm{Fbar}\,i) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F$ over $L$ (pairs of ring automorphisms of $F$ and of $L$ compatible with $L \to F$) such that each $s \in S$ preserves $A$, fixes $\pi$, acts trivially on the residue field of $A$, preserves every chart and annulus domain, fixes both parameters of every annulus, preserves each chart's integers with unchanged residue, and commutes with each place map; assume further that every ring automorphism of $L$ with these three properties on $(A,\pi)$ is the base automorphism of some $s \in S$. Let $\ell$ be a prime invertible in the residue field of $A$, assume some $s \in S$ moves an $\ell$-th root of $\pi$, and assume the rational Tate module $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$. Finally let $M$ be a semistable model of these data over $A$ and $D$ a descent datum for $M$. Then for every $s_0 \in S$ for which there is $r \in L$ with $r^\ell = \pi$ and $s_0$ moving $r$, the kernel of $\rho(s_0) - 1$ on the rational Tate module, where $\rho$ is the representation of the group of semilinear automorphisms on $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F/L))$, equals the intersection over all $s \in S$ of the kernels of $\rho(s) - 1$.
--
--   This is the statement that a single inertia element with non-trivial tame character at $\ell$ already cuts out the full space of $S$-invariants in the $\ell$-adic Tate module of the Jacobian of a semistable curve, the form in which Grothendieck's description of inertia acting through $\sigma \mapsto \exp(t_\ell(\sigma)N)$ is used in practice. It feeds the computation of the image of inertia on $\mathrm{Pic}^0$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ker_sub_one_eq_iInf_ker_of_pow_eq_of_baseAut_ne_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.ker_sub_one_eq_iInf_ker_of_pow_eq_of_baseAut_ne_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    ∀ s₀ ∈ S, (∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s₀ r ≠ r) →
      LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s₀ - 1) =
        ⨅ s ∈ S, LinearMap.ker (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s - 1) := by sorry
