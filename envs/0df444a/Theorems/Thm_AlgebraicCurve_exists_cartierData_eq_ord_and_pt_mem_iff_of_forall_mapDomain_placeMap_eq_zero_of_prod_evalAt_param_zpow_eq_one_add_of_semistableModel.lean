-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
-- name    : AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/484f80a1-123c-5d95-acf3-9394afb96dcb
-- title:
--   Cartier data for reduction-trivial divisors on a semistable model
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with a nonzero element $\pi$ of its maximal ideal, subject to the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power $y^{n}$ has valuation at most that of $x$; let $F$ be a field extension of $L$ which is a curve over $L$ (in the sense of `IsCurveOver`: principal divisors of degree zero exist, residue fields of places are finite over $L$, and $\Omega_{F/L}$ is free of rank one) and essentially of finite type, and let $\bar F_0,\dots,\bar F_{n-1}$ be curves over the residue field of $A$, essentially of finite type, all of whose places are rational. The remaining data form a semistable covering: component charts $C_i$ (valuation subrings of $F$ with residue map onto $\bar F_i$, a domain of places, a finite set of nodes and a reduction map `placeMap`) all of whose domain places are rational; annuli $\mathrm{An}_e$, $\mathrm{An}'_e$ for $e < m$ with the same domain and the same modulus, the modulus nonzero and of the form (unit)$\cdot\pi^{w_e}$, and with $\mathrm{An}'_e.\mathrm{param} \cdot \mathrm{An}_e.\mathrm{param}$ the image of that modulus; edge maps $\mathrm{src}, \mathrm{tgt}$ and node places $x^s_e, x^t_e$ such that $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x^s_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x^t_e$; each node of each chart is the image of exactly one of the $2m$ edge ends; every place of $F/L$ lies either in exactly one chart domain and in no annulus, or in exactly one annulus domain and in no chart; every non-nodal place $Q$ of $\bar F_i$ admits a chart function $T$ with nonzero residue of $Q$-order one, taking values in the maximal ideal of $A$ at all places above $Q$ and assuming each such value at exactly one place above $Q$; and the genus relation $g(F/L) + n = \sum_i g(\bar F_i) + m + 1$ holds. Let $M$ be a `SemistableModel` for these data, with scheme $X = M.X$, function field identification $M.\mathrm{ffEquiv}$ and point map $M.\mathrm{pt}$. Finally, let $G_i$ be divisors on $F/L$ supported in $(C_i).\mathrm{dom}$ whose push-forward $\mathrm{mapDomain}\,(C_i).\mathrm{placeMap}\,G_i$ vanishes, and let $N_e$ be divisors supported in $(\mathrm{An}_e).\mathrm{dom}$ of total mass zero such that $\prod_P (P.\mathrm{evalAt}\,(\mathrm{An}_e).\mathrm{param})^{N_e(P)} = 1 + t$ for some $t$ in the maximal ideal of $A$. Put $G = \sum_i G_i + \sum_e N_e$. The conclusion asserts the existence of finitely many open subsets $U_a$ ($a < r$) of $X$ with $\bigsqcup_a U_a = \top$ and nonzero elements $h_a \in F$ such that: $\mathrm{ord}_P(h_a) = G(P)$ whenever $M.\mathrm{pt}\,P \in U_a$; for all $a, b$ and all $x \in U_a \cap U_b$ one has $h_a = h_b\,(1 + \iota(t)\,\rho)$ with $t$ in the maximal ideal of $A$ and $\rho$ in the subring `SemistableModel.localRing M.X M.ffEquiv x` of $F$ (the image of the stalk at $x$); some index $a_0$ satisfies $M.\mathrm{pt}\,P \in U_{a_0} \iff G(P) = 0$; and each $U_a$ has one of three traces on the points $M.\mathrm{pt}\,P$, namely $\{G(P) = 0\}$, or $\{P \in (C_i).\mathrm{dom},\ (C_i).\mathrm{placeMap}\,P = q\} \cup \{G(P) = 0,\ \mathrm{ord}_P(h_a) = 0\}$ for some $i$ and some place $q$ of $\bar F_i$, or $(\mathrm{An}_{e_0}).\mathrm{dom} \cup \{G(P) = 0,\ \mathrm{ord}_P(h_a) = 0\}$ for some edge $e_0$.
--
--   This produces Cartier-type local data on a semistable model for a divisor assembled from chart parts with vanishing reduction and residue-balanced annulus parts of total mass zero: an open cover together with local equations whose transition functions are congruent to $1$ modulo the maximal ideal of $A$, so that the associated Cartier divisor has trivial reduction on the special fibre. It is used by [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent), in the analysis of reduction on prime-to-$p$ torsion of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_prod_evalAt_param_zpow_eq_one_add_of_semistableModel
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
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
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt)
    (Gi : Fin n → Divisor L F) (hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0)
    (N : Fin m → Divisor L F) (hN : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hmass : ∀ e, ((N e).sum fun _ k => k) = 0)
    (hbalN : ∀ e, ∃ t ∈ IsLocalRing.maximalIdeal A,
      ((N e).prod fun P k => (P.evalAt (An e).param) ^ k) = 1 + ((t : A) : L)) :
    ∃ (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F),
      (⨆ a, U a) = ⊤ ∧ (∀ a, h a ≠ 0) ∧
      (∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        (∑ i, Gi i + ∑ e, N e) P) ∧
      (∀ a b (x : M.X), x ∈ U a → x ∈ U b →
        ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
          h a = h b * (1 + algebraMap L F ((t : A) : L) * r)) ∧
      (∃ a₀, ∀ P : Place L F, M.pt P ∈ U a₀ ↔
        (∑ i, Gi i + ∑ e, N e) P = 0) ∧
      (∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔
          (∑ i, Gi i + ∑ e, N e) P = 0) ∨
        (∃ (i : Fin n) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨
            ((∑ i, Gi i + ∑ e, N e) P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : Fin m, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨
            ((∑ i, Gi i + ∑ e, N e) P = 0 ∧ P.ord (h a) = 0)))) := by sorry
