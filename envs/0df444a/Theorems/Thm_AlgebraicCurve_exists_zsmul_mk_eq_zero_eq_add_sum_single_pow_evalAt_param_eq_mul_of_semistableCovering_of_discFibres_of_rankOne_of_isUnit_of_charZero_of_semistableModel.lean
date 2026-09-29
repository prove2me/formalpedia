-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel
-- name    : AlgebraicCurve.exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/04434cf4-84d7-5738-831e-63a22bd84bb5
-- title:
--   ℓ-power torsion classes with prescribed depths along annuli
-- statement:
--   Let $L$ be an algebraically closed field of characteristic zero, $A \subseteq L$ a valuation subring with residue field $\kappa$, and $\pi \in A$ a nonzero element of the maximal ideal; assume the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ in the project's sense (principal divisors exist, every place has residue field finite over $L$, and $\Omega_{F/L}$ is free of rank one over $F$) and essentially of finite type over $L$, and let $\bar F_i$, $i \in \{0,\dots,n-1\}$, be curves over $\kappa$, essentially of finite type, all of whose places are rational (i.e. $\kappa$ surjects onto the residue field). The covering data consist of component charts $C_i$ — a valuation subring of $F$ with surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a set $\mathrm{dom}(C_i)$ of places of $F/L$ all of which are rational, a finite set $\mathrm{nodes}(C_i)$ of places of $\bar F_i/\kappa$, and a reduction map on places, subject to the compatibilities in `ComponentChart` — together with annuli $\mathrm{An}_e, \mathrm{An}'_e$ for $e \in \{0,\dots,m-1\}$, each given by a domain of places, a parameter and a modulus in the maximal ideal of $A$ with the properties in `Annulus`, end maps $\mathrm{src},\mathrm{tgt}$ and node places $x^{\mathrm s}_e, x^{\mathrm t}_e$, and widths $w_e \in \mathbb N$. The hypotheses are: $\mathrm{An}'_e$ has the same domain and modulus as $\mathrm{An}_e$, this modulus is nonzero in $L$ and the product of the two parameters is the image of the modulus; each modulus equals $u\pi^{w_e}$ for a unit $u \in A^{\times}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{\mathrm s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{\mathrm t}_e$ in the sense of `IsAttached`; every node of every chart is an end of exactly one edge end (existence, and uniqueness over the disjoint union of source and target ends); every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i/\kappa$ there is $T$ in the integers of $C_i$ with nonzero residue and $\mathrm{ord}_Q(\mathrm{res}\,T) = 1$ such that all places of $\mathrm{dom}(C_i)$ reducing to $Q$ evaluate $T$ into the maximal ideal of $A$, and each element of that maximal ideal is $P.\mathrm{evalAt}\,T$ for a unique such $P$ (a disc fibre over $Q$); and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/\kappa) + m + 1$. Finally, $\ell$ is a prime which is a unit in $\kappa$, $k > 0$, there are a semistable model $M$ over $A$ for this data and a descent $\mathcal D$ of it, and every element $a$ of $\kappa$ satisfies $a^{p^{n}} = a$ for some $n > 0$, where $p$ is the characteristic of $\kappa$ when it is positive. The conclusion: for every $n_0 : \{0,\dots,m-1\} \to \mathbb Z$ there are a divisor $D$ on $F/L$ of degree zero whose class in $\mathrm{Pic}^0$ is killed by $\ell^{K}$ for some $K \in \mathbb N$, a divisor $D_{\mathrm{ch}}$ supported in the union of the chart domains, places $Q_e \in \mathrm{dom}(\mathrm{An}_e)$ with $(Q_e.\mathrm{evalAt}\,z_e)^{\ell^k} = v\pi$ for some $v \in A^{\times}$, where $z_e$ is the parameter of $\mathrm{An}_e$, and integers $n_e \equiv n_0(e) \pmod{\ell^k}$, such that $D = D_{\mathrm{ch}} + \sum_e n_e\,[Q_e]$. The existentially bound divisor in the conclusion is named $D$ as well, shadowing the descent; no lower bound such as $K \ge k$ is asserted on the exponent $K$.
--
--   The statement produces degree-zero divisor classes of $\ell$-power order on a curve with semistable reduction whose support realises a prescribed position, to precision $\ell^k$, along the annuli of a semistable covering — the divisor-theoretic counterpart of prescribing the depth of a torsion point on the edges of the dual graph. It is used in the construction of the $\ell$-adic Tate module of the Jacobian in terms of the covering, in the theorem on quadruples of annulus data that cites it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel.lean

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
    AlgebraicCurve.exists_zsmul_mk_eq_zero_eq_add_sum_single_pow_evalAt_param_eq_mul_of_semistableCovering_of_discFibres_of_rankOne_of_isUnit_of_charZero_of_semistableModel
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A)) (k : ℕ)
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (hk : 0 < k)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    :
    ∀ n₀ : Fin m → ℤ,
      ∃ (D : Divisor L F) (hD : D ∈ Divisor.degZero (K := L) (F := F)),
        (∃ K : ℕ, ((ℓ ^ K : ℕ) : ℤ) • Pic0.mk ⟨D, hD⟩ = 0) ∧
        ∃ (Dch : Divisor L F) (Q : Fin m → Place L F) (nn : Fin m → ℤ),
          (∀ P ∈ Dch.support, ∃ i, P ∈ (C i).dom) ∧
          (∀ e, Q e ∈ (An e).dom ∧ ∃ v : Aˣ, (((Q e).evalAt (An e).param) ^ (ℓ ^ k) = ((v : A) : L) * (π : L))) ∧
          (∀ e, ((ℓ ^ k : ℕ) : ℤ) ∣ nn e - n₀ e) ∧
          D = Dch + ∑ e, nn e • Finsupp.single (Q e) 1 := by sorry
