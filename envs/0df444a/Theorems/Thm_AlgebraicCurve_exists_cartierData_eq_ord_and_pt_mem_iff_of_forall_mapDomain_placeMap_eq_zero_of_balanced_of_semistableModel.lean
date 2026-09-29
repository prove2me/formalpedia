-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel
-- name    : AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/9ecf18bb-0e85-5db1-ba78-c0ce20708fca
-- title:
--   Cartier data for a balanced divisor on a semistable model
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $\pi \in \mathfrak m_A$ nonzero, and assume $A$ has rank one in the sense that for every $x \in L^\times$ and every $y \in \mathfrak m_A$ some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$, let $\iota V,\iota E$ be finite, let $(\bar F_i)_{i \in \iota V}$ be extensions of the residue field $k = A/\mathfrak m_A$ all of whose places are rational (the structural map $k \to$ residue field being surjective), and let $C_i$ be component charts of $F$ over $\bar F_i$, all places in $(C_i).\mathrm{dom}$ being rational. Given annuli $\mathrm{An}_e, \mathrm{An}'_e$ indexed by $\iota E$, maps $\mathrm{src},\mathrm{tgt} : \iota E \to \iota V$, node places $x^s_e,x^t_e$ and weights $w_e \in \mathbb N$, assume: each pair $\mathrm{An}'_e,\mathrm{An}_e$ has the same domain and the same modulus, that modulus is nonzero in $L$, and the product of the two parameters is the image of the modulus; each modulus is a unit times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^s_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^t_e$; every node of every chart is the end of exactly one edge-end (existence, and uniqueness over $\iota E \sqcup \iota E$); every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each chart $i$ and each non-node place $Q$ of $\bar F_i$ there is a function $T$ in the chart's valuation ring whose residue is nonzero with $\mathrm{ord}_Q = 1$, lying in the valuation ring of every $P$ over $Q$ with $P(T) \in \mathfrak m_A$, and such that each $c \in \mathfrak m_A$ is the value $P(T)$ of a unique $P$ in the chart domain over $Q$; and the genus relation $g(F/L) + \#\iota V = \sum_i g(\bar F_i/k) + \#\iota E + 1$ holds, with $F/L$ and each $\bar F_i/k$ curves in the sense of `IsCurveOver` and essentially of finite type. Let $M$ be a semistable model for these data, let $G_i$ be divisors of $F/L$ supported in $(C_i).\mathrm{dom}$ whose push-forwards $\mathrm{mapDomain}\,(C_i).\mathrm{placeMap}\,G_i$ vanish, and let $e : \iota \to \iota E$, $n_j \in \mathbb Z$ and places $Q_{j,l} \in \mathrm{An}_{e(j)}.\mathrm{dom}$ ($l \in \{0,1,2,3\}$, $\iota$ finite) satisfy, writing $z$ for the parameter of $\mathrm{An}_{e(j)}$ and $z(P) = P.\mathrm{evalAt}\,z$, the radius condition $z(Q_{j,0}) = u\, z(Q_{j,2})$ with $u \in A^\times$ and the balance condition $z(Q_{j,0})z(Q_{j,1}) = z(Q_{j,2})z(Q_{j,3})(1+t)$ with $t \in \mathfrak m_A$. Put $G = \sum_i G_i + \sum_j n_j\big((Q_{j,0})+(Q_{j,1})-(Q_{j,2})-(Q_{j,3})\big)$. Then there exist $r \in \mathbb N$, open subsets $U_a$ of $M.X$ ($a \in \mathrm{Fin}\,r$) covering $M.X$, and nonzero $h_a \in F$ such that: $\mathrm{ord}_P(h_a) = G(P)$ whenever $M.\mathrm{pt}(P) \in U_a$; for all $a,b$ and all $x \in U_a \cap U_b$ one has $h_a = h_b\,(1 + t\,r)$ for some $t \in \mathfrak m_A$ and some $r$ in the image in $F$ of the local ring of $M.X$ at $x$; some $U_{a_0}$ has generic trace exactly $\{P : G(P) = 0\}$; and each $U_a$ has generic trace either $\{P : G(P)=0\}$, or, for one chart $i$ and one place $q$ of $\bar F_i$, the set of $P$ with ($P \in (C_i).\mathrm{dom}$ and $(C_i).\mathrm{placeMap}\,P = q$) or ($G(P) = 0$ and $\mathrm{ord}_P(h_a) = 0$), or, for one edge $e_0$, the set of $P$ with $P \in \mathrm{An}_{e_0}.\mathrm{dom}$ or ($G(P)=0$ and $\mathrm{ord}_P(h_a)=0$).
--
--   This is the construction of Cartier data for the divisor $G$ on a semistable model: a finite trivialising cover on which $G$ is cut out by single functions, whose transition factors are congruent to $1$ modulo $\mathfrak m_A$, together with explicit control of the traces of the cover on the generic fibre. It is used in the descent step [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent), where the unipotent cocycle condition converts a multiple of $G$ being principal into $G$ itself being principal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_cartierData_eq_ord_and_pt_mem_iff_of_forall_mapDomain_placeMap_eq_zero_of_balanced_of_semistableModel
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
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
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt)
    (Gi : ιV → Divisor L F) (hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0)
    {ι : Type*} [Fintype ι] (e : ι → ιE) (nq : ι → ℤ) (Q : ι → Fin 4 → Place L F)
    (hQ : ∀ j l, Q j l ∈ (An (e j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
        (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L))) :
    ∃ (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F),
      (⨆ a, U a) = ⊤ ∧ (∀ a, h a ≠ 0) ∧
      (∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P) ∧
      (∀ a b (x : M.X), x ∈ U a → x ∈ U b →
        ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
          h a = h b * (1 + algebraMap L F ((t : A) : L) * r)) ∧
      (∃ a₀, ∀ P : Place L F, M.pt P ∈ U a₀ ↔
        (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0) ∧
      (∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔
          (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨
            ((∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨
            ((∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0 ∧ P.ord (h a) = 0)))) := by sorry
