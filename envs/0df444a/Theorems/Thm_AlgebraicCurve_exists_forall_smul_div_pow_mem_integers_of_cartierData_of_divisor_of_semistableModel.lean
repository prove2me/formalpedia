-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
-- name    : AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/0239fe5c-97fd-52b5-a883-f85d4cb1441c
-- title:
--   Vertical unit constants for Cartier data on a semistable model
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring with a nonzero element $\pi$ of its maximal ideal, and assume $A$ has rank one in the form: for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ there is $n$ with $v_A(y^n) \le v_A(x)$. Let $F$ be a field extension of $L$, let $\iota_V,\iota_E$ be finite index types, and for $i \in \iota_V$ let $Fbar\,i$ be an extension of the residue field of $A$, all of whose places are rational (the structure map to the residue field of a place is surjective), together with a `ComponentChart` $C\,i$ all of whose places in the domain are rational. Edge data consist of annuli $An\,e, An'\,e$, maps $src,tgt : \iota_E \to \iota_V$, node places $xs\,e$ on $Fbar(src\,e)$ and $xt\,e$ on $Fbar(tgt\,e)$, and weights $w : \iota_E \to \mathbb{N}$, subject to: `hpair`, the two annuli of an edge share domain and modulus, the modulus is nonzero in $L$ and the product of the two parameters is the image of the modulus; `hw`, the modulus of $An\,e$ is a unit times $\pi^{w(e)}$; `hatt`, $An\,e$ is attached to $(C(src\,e),xs\,e)$ and $An'\,e$ to $(C(tgt\,e),xt\,e)$; `hnodes`, every node of every chart is an endpoint of some edge, and the two endpoint assignments $\iota_E \sqcup \iota_E \to \Sigma_j\,\mathrm{Place}(Fbar\,j)$ are injective on nodes; `hcover`, each place of $F/L$ lies in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; `hdisc`, for each chart $i$ and each non-node place $Q$ of $Fbar\,i$ there is $T$ in the chart's integers with nonzero residue of $Q$-order $1$, lying in every place of the domain above $Q$ with evaluation in the maximal ideal of $A$, and such that every element of the maximal ideal is the evaluation of $T$ at a unique place of the domain above $Q$; and `hgenus`, $g(F/L) + \#\iota_V = \sum_i g(Fbar\,i/\kappa_A) + \#\iota_E + 1$. Assume $F/L$ and each $Fbar\,i/\kappa_A$ are curves (principal divisors exist, finite residue fields, $\Omega$ free of rank one) and essentially of finite type, and let $M$ be a `SemistableModel` for this data. Let $G$ be a divisor on $F/L$, $k > 0$, and $g \neq 0$ with $\mathrm{ord}_P\,g = k\,G(P)$ for every place $P$. Let $U : \mathrm{Fin}\,r \to$ opens of $M.X$ cover $M.X$, and $h : \mathrm{Fin}\,r \to F$ with each $h\,a \neq 0$, such that $\mathrm{ord}_P(h\,a) = G(P)$ whenever $M.\mathrm{pt}\,P \in U\,a$, and on each overlap $x \in U\,a \cap U\,b$ one has $h\,a = h\,b\,(1 + t\,r)$ for some $t$ in the maximal ideal of $A$ and some $r$ in the local ring of $M.X$ at $x$, regarded as a subring of $F$ through the function-field identification. Then there exist constants $c : \iota_V \to L$, all nonzero, such that for all $i$ and $a$ with $M.\mathrm{gen}\,i \in U\,a$ both $c_i\,(g/(h\,a)^k)$ and its inverse lie in $(C\,i).\mathrm{integers}$, and such that $v_A(c_{src\,e}) = v_A(c_{tgt\,e})$ for every edge $e$.
--
--   This is the statement that Cartier data $(U_a,h_a)$ for a divisor $G$ on a semistable covering can be normalised componentwise: after scaling by a vertical constant, $g/h_a^{k}$ becomes a unit of the chart ring attached to each component, and the constants have equal valuation along every edge of the dual graph, so that the associated slopes are harmonic and vanish. It feeds the descent step [`AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.sum_mem_principal_of_zsmul_mem_principal_of_isNodalPrincipal_mapDomain_placeMap_of_semistableModel_of_descent), where principality of a divisor whose reduction is a nodal principal datum is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_forall_smul_div_pow_mem_integers_of_cartierData_of_divisor_of_semistableModel
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
    (G : Divisor L F)
    (k : ℕ) (hk : 0 < k) (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) *
      G P)
    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (hU : (⨆ a, U a) = ⊤) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        G P)
    (hcoc : ∀ a b (x : M.X), x ∈ U a → x ∈ U b →
      ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
        h a = h b * (1 + algebraMap L F ((t : A) : L) * r)) :
    ∃ c : ιV → L, (∀ i, c i ≠ 0) ∧
      (∀ i a, M.gen i ∈ U a →
        c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers) ∧
      (∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e'))) := by sorry
