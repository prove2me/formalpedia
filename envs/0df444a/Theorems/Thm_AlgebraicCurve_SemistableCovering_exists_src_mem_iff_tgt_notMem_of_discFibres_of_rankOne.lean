-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/b05eade5-79a9-5d24-be9b-4862456e2f1a
-- title:
--   Incidence graph of a semistable covering is connected
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, $\pi$ a nonzero element of its maximal ideal, and assume $A$ has rank one in the form: for every nonzero $x \in L$ and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $v_A(y^n) \le v_A(x)$. Let $F$ be a field over $L$, and let $\bar F_0,\dots,\bar F_{n-1}$ be fields over the residue field $\kappa$ of $A$, all of whose places are rational (the structure map $\kappa \to$ residue field of the place is surjective), with $F/L$ and each $\bar F_i/\kappa$ curves in the sense of `IsCurveOver` (principal divisors of degree zero, finite residue extensions, free rank-one module of Kähler differentials) and essentially of finite type. Given for each $i$ a component chart $C_i$ of type `ComponentChart A F (Fbar i)` — a valuation subring of $F$ (its integers), a surjective residue homomorphism onto $\bar F_i$ with kernel the maximal ideal, a set of places of $F$ (its domain), a finite set of nodes among places of $\bar F_i$, and a place map, subject to the compatibility axioms of that structure — all places in the chart domains being rational; and given annuli $An_e, An'_e$ ($e \in \{0,\dots,m-1\}$), maps $\mathrm{src},\mathrm{tgt}$ to chart indices, places $xs_e$ of $\bar F_{\mathrm{src}(e)}$ and $xt_e$ of $\bar F_{\mathrm{tgt}(e)}$, and weights $w_e \in \mathbb{N}$, subject to: $An'_e$ has the same domain and modulus as $An_e$, the modulus is nonzero in $L$ and the product of the two parameters is the image of the modulus; each modulus is a unit times $\pi^{w_e}$; $An_e$ is attached to $(C_{\mathrm{src}(e)}, xs_e)$ and $An'_e$ to $(C_{\mathrm{tgt}(e)}, xt_e)$ in the sense of `IsAttached`; every node of every chart is an end of at least one annulus and of exactly one (the map from $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$ sending $e$ to $(\mathrm{src}(e), xs_e)$, resp. $(\mathrm{tgt}(e), xt_e)$, is injective onto the nodes); every place of $F$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; each fibre of each place map over a non-node $Q$ is a disc, i.e. there is $T$ in the chart's integers whose residue is nonzero with $\mathrm{ord}_Q = 1$, which lies in the valuation subring of every place of the chart domain above $Q$ with value in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one place $P$ of the chart domain above $Q$ with $P(T) = c$; and the genus identity $g(F) + n = \sum_i g(\bar F_i) + m + 1$ for the genera `genusFF`. Then for every finite set $S$ of chart indices with $S$ and its complement both nonempty there exists an annulus index $e$ with $\mathrm{src}(e) \in S$ if and only if $\mathrm{tgt}(e) \notin S$, i.e. some annulus joins $S$ to its complement.
--
--   This is the connectedness of the incidence graph of a semistable covering — vertices the $n$ component charts, edges the $m$ annuli — expressed as the statement that no nonempty proper set of charts is separated from its complement; in geometric terms, the connectedness of the special fibre of a semistable model. It is used by the results computing divisor classes and principal divisors on such a covering, where the count of toric classes killed by a given integer depends on the first cohomology of a connected graph.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.exists_src_mem_iff_tgt_notMem_of_discFibres_of_rankOne
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
    :
    ∀ S : Finset (Fin n), S.Nonempty → Sᶜ.Nonempty → ∃ e : Fin m, (src e ∈ S ↔ tgt e ∉ S) := by sorry
