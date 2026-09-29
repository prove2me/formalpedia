-- Prove2me | Theorems.Thm_AlgebraicCurve_rationalGaloisRep_apply_sub_eq_sub_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.rationalGaloisRep_apply_sub_eq_sub_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/a5263191-3513-5112-b41c-45d2e18564a6
-- title:
--   Level-two monodromy law on the rational Tate module
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, and $\pi \in A$ a non-zero element of the maximal ideal; assume $A$ has rank one in the sense that for every non-zero $x \in L$ and every $y$ in the maximal ideal some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a one-variable function field over $L$ (`IsCurveOver L F`) and essentially of finite type, and let semistable covering data be given: fields $\bar F_i$ over the residue field of $A$ for $i \in \mathrm{Fin}\,n$, each a one-variable function field of finite type all of whose places are rational; component charts $C_i$ (a valuation subring of $F$ with surjective residue map onto $\bar F_i$, a set of places of $F/L$, a finite set of nodes, and a place map), all places in the chart domains being rational; annuli $\mathrm{An}_e, \mathrm{An}'_e$ for $e \in \mathrm{Fin}\,m$ with maps $\mathrm{src},\mathrm{tgt}$ to the charts and node points $x^s_e, x^t_e$; and weights $w_e \in \mathbb{N}$. The hypotheses on these data, summarised here, are: paired annuli have equal domains and moduli, with non-zero modulus and the product of the two parameters equal to the image of the modulus; each modulus is a unit times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^s_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^t_e$; every node of every chart is an end of exactly one of the $2m$ annulus ends; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; each fibre of a chart place map over a non-node point $Q$ carries a function $T$ in the chart integers whose residue has order one at $Q$, lying in the maximal ideal at every place over $Q$ and taking each value in the maximal ideal of $A$ at exactly one such place; and the genus identity $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F$ (pairs of a ring automorphism of $F$ and one of $L$ compatible with $L \to F$) such that every $s \in S$ has base automorphism preserving $A$, fixing $\pi$ and inducing the identity on the residue field, preserves each chart domain and each annulus domain and each chart's integers with its residue map, fixes every parameter $\mathrm{An}_e.\mathrm{param}$ and $\mathrm{An}'_e.\mathrm{param}$, and commutes with every chart place map; assume every automorphism of $L$ with those three properties on $A$, $\pi$ and the residue field is the base automorphism of some member of $S$. Let $\ell$ be a prime invertible in the residue field of $A$, assume some $s \in S$ moves an $\ell$-th root of $\pi$, and assume the rational Tate module $\mathbb{Q}_\ell \otimes_{\mathbb{Z}_\ell} T_\ell(\mathrm{Pic}^0(F/L))$ is finite-dimensional over $\mathbb{Q}_\ell$, where $\mathrm{Pic}^0$ is the group of degree-zero divisors of $F/L$ modulo principal divisors. Finally let $M$ be a semistable model of these data over $A$ (an integral scheme, proper, flat and locally of finite presentation over $\mathrm{Spec}\,A$, with function field identified with $F$ and with prescribed points for the places, the chart integers, the non-node residue places and the annuli) together with a descent datum $D : M.\mathrm{Descent}$ exhibiting it as a base change along a local injection into $A$ from a Noetherian Henselian local ring. Then for all $s, s' \in S$ and every $v$ in the rational Tate module, $\rho(s')\bigl(\rho(s)v - v\bigr) = \rho(s)v - v$, where $\rho$ denotes [`ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F)`](def/ModularCurve_JZeroTateModule.html#L48).
--
--   This is the level-two law $(\rho(s') - 1)(\rho(s) - 1) = 0$ for the $\ell$-adic monodromy action on the rational Tate module of $\mathrm{Pic}^0$ of a curve with semistable reduction: every monodromy difference $\rho(s)v - v$ is fixed by all of $S$. It is used in both directions of the kernel description of the monodromy filtration, where it places $\rho(s)v - v$ in the part of the Tate module on which reduction is defined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_rationalGaloisRep_apply_sub_eq_sub_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.rationalGaloisRep_apply_sub_eq_sub_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_charZero_of_semistableModel
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
    ∀ s ∈ S, ∀ s' ∈ S, ∀ v : ModularCurve.RationalTateModule ℓ (Pic0 L F),
      ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s' (ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s v - v) = ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s v - v := by sorry
