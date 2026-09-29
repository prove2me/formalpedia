-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/b49fdda8-8a18-5888-9a91-b1b6b7490782
-- title:
--   Lifting ℓ-power torsion tropical positions to divisor classes
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring, $\pi \in A$ a nonzero element of the maximal ideal, and assume $A$ has rank one in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (`IsCurveOver`, i.e. principal divisors, finite residue extensions, and $\Omega_{F/L}$ free of rank one over $F$) and essentially of finite type, and let $\overline{F}_i$, $i \in \mathrm{Fin}\,n$, be curves over the residue field of $A$, essentially of finite type, all of whose places are rational. The covering data consist of: component charts $C_i$ (valuation subrings of $F$ with residue map onto $\overline{F}_i$, a domain of places, a finite set of nodes and a reduction map on places), all places in the chart domains being rational; annuli $An_e, An'_e$, $e \in \mathrm{Fin}\,m$, with the same domain and modulus, with modulus nonzero in $L$ and with the product of the two parameters equal to the modulus; maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$ and node places $x_s(e), x_t(e)$ to which $An_e$ and $An'_e$ are attached; widths $w_e$ with $An_e$'s modulus a unit times $\pi^{w_e}$; the condition that each node of each chart is an endpoint of exactly one of the $2m$ annulus ends; the condition that every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; a discoid condition providing, for each chart $C_i$ and each non-node place $Q$ of $\overline{F}_i$, a function $T$ in the chart's valuation subring whose residue has order $1$ at $Q$, which is integral with residue in the maximal ideal at every place of the chart domain reducing to $Q$, and for which evaluation of $T$ identifies that fibre bijectively with the maximal ideal of $A$; and the genus relation $g(F/L) + n = \sum_i g(\overline{F}_i) + m + 1$. Further let $\ell$ be a prime invertible in the residue field, $K \in \mathbb{N}$, let $M$ be a semistable model of this data over $A$ together with a descent of $M$ to a Noetherian henselian local subring, let $\varpi$ be an element of the maximal ideal with $\varpi^{\ell^{K}} = \pi$, and assume the residue field is locally finite, i.e. in residue characteristic $p$ every element $a$ satisfies $a^{p^{n}} = a$ for some $n > 0$. Put $V = \mathrm{Fin}\,n \sqcup \coprod_e \mathrm{Fin}(\ell^{K}w_e - 1)$, the vertex set of the $\ell^{K}$-fold subdivision of the dual graph, with the indicated endpoint map on the $\ell^{K}w_e$ subdivided edges and with `lap` the associated graph Laplacian, $\mathrm{lap}(u)$ being the corresponding column function $V \to \mathbb{Z}$. The assertion is: for every additive map $\mu$ from divisors on $F/L$ to $V \to \mathbb{Z}$ which sends a place of the domain of $C_i$ to the indicator of the vertex $i$, a place $P$ of the domain of $An_e$ at which the parameter evaluates to a unit times $\varpi^{d}$ with $0 < d < \ell^{K}w_e$ to the indicator of the interior vertex $(e, d-1)$, and a place of an annulus domain at which the parameter's evaluation is not of the form (unit)$\cdot\varpi^{d}$ to $0$; and for every $t : V \to \mathbb{Z}$ such that $\ell^{K''}t$ agrees with some integral Laplacian combination $\sum_u \varphi(u)\,\mathrm{lap}(u)$ at all interior vertices, for some $K''$ and $\varphi$: there exist a degree-zero divisor $D$ on $F/L$ and $\chi : V \to \mathbb{Z}$ such that $\ell^{K'}$ annihilates the class of $D$ in $\mathrm{Pic}^{0}$ for some $K'$, every place in the support of $D$ lies in some chart domain or in some annulus domain with the parameter evaluating to a unit times a power of $\varpi$, and $\mu(D)(v) - t(v) = \bigl(\sum_u \chi(u)\,\mathrm{lap}(u)\bigr)(v)$ at every interior vertex $v$.
--
--   This is the surjectivity of the specialisation map from $\ell$-power torsion in $\mathrm{Pic}^{0}$ of the curve onto the $\ell$-power torsion of the tropical Jacobian of the $\ell^{K}$-subdivided dual graph, stated in the chart language of semistable coverings and only at the interior vertices of the subdivision, with the lifted class represented by a divisor supported on chart places and $\varpi$-lattice points of the annuli. It is used in the next step of the chain, which converts such a lift into an explicit divisor of the form prescribed by the position datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.exists_pow_zsmul_mk_eq_zero_forall_mu_sub_eq_sum_smul_lap_of_semistableCovering_of_discFibres_of_rankOne_of_charZero_of_semistableModel
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A)) (K : ℕ)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (ϖ : A) (hϖ : ϖ ∈ IsLocalRing.maximalIdeal A) (hϖπ : ϖ ^ (ℓ ^ K) = π)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    :
    let V := Fin n ⊕ (Σ e : Fin m, Fin (ℓ ^ K * w e - 1))
    let ends : (Σ e : Fin m, Fin (ℓ ^ K * w e)) → V × V := fun ε =>
      (if h0 : ε.2.1 = 0 then Sum.inl (src ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1 - 1, by have := ε.2.2; omega⟩⟩,
       if h1 : ε.2.1 + 1 = ℓ ^ K * w ε.1 then Sum.inl (tgt ε.1)
        else Sum.inr ⟨ε.1, ⟨ε.2.1, by have := ε.2.2; omega⟩⟩)
    let lap : V → (V → ℤ) := fun v => ∑ ε : Σ e : Fin m, Fin (ℓ ^ K * w e),
      ((if (ends ε).1 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).2 1 : V → ℤ) else 0) +
       (if (ends ε).2 = v then (Pi.single v 1 : V → ℤ) - (Pi.single (ends ε).1 1 : V → ℤ) else 0))
    ∀ μ : Divisor L F →+ (V → ℤ),
      (∀ i, ∀ P ∈ (C i).dom, μ (Finsupp.single P 1) = Pi.single (Sum.inl i) 1) →
      (∀ e, ∀ P ∈ (An e).dom, ∀ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
        (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d → ∀ (hd0 : 0 < d) (hdw : d < ℓ ^ K * w e),
          μ (Finsupp.single P 1) = Pi.single (Sum.inr ⟨e, ⟨d - 1, by omega⟩⟩) 1) →
      (∀ e, ∀ P ∈ (An e).dom,
        (¬ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
          (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) → μ (Finsupp.single P 1) = 0) →
      ∀ t : V → ℤ,
        (∃ (K'' : ℕ) (φ : V → ℤ), ∀ v : Σ e : Fin m, Fin (ℓ ^ K * w e - 1),
            (ℓ ^ K'' : ℤ) * t (Sum.inr v) = (∑ u, φ u • lap u) (Sum.inr v)) →
        ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)) (χ : V → ℤ),
          (∃ K' : ℕ, ((ℓ ^ K' : ℕ) : ℤ) • Pic0.mk ⟨D, hD⟩ = 0) ∧
          (∀ P ∈ D.support, (∃ i, P ∈ (C i).dom) ∨
            ∃ e, P ∈ (An e).dom ∧ ∃ (d : ℕ) (u : Aˣ) (h : P.evalAt (An e).param ∈ A),
              (⟨P.evalAt (An e).param, h⟩ : A) = u * ϖ ^ d) ∧
          ∀ v : Σ e : Fin m, Fin (ℓ ^ K * w e - 1), μ D (Sum.inr v) - t (Sum.inr v) = (∑ u, χ u • lap u) (Sum.inr v) := by sorry
