-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/bde6f56c-ad22-568a-a4fa-083807aaaf50
-- title:
--   Chart residues of a Riemann–Roch space are independent
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with residue field $\kappa = \mathrm{ResidueField}\ A$; let $\pi$ be a nonzero element of the maximal ideal of $A$, and assume $A$ has rank one in the form: for every $x \in L^{\times}$ and every $y$ in the maximal ideal there is $n \in \mathbb{N}$ with $v_A(y^{n}) \le v_A(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ and of essentially finite type, and let $n, m \in \mathbb{N}$, $\bar F_1,\dots,\bar F_n$ fields over $\kappa$, each a curve over $\kappa$ of essentially finite type, all of whose places are rational (the structure map of $\kappa$ into the residue field of the place being surjective). The remaining data are the pieces of a semistable covering of $F$ along $A$: component charts $C_i : \mathrm{ComponentChart}\ A\ F\ \bar F_i$ (a valuation subring $\mathcal O_i$ of $F$, a surjective residue homomorphism onto $\bar F_i$ with kernel the maximal ideal, a domain $\mathrm{dom}$ of places of $F/L$ all of which are assumed rational, a finite set of nodes among the places of $\bar F_i/\kappa$, and a map from places of $F$ to places of $\bar F_i$ satisfying the chart axioms); two families of annuli $\mathrm{An}(e), \mathrm{An}'(e)$ indexed by $e \in \mathrm{Fin}\ m$ with the same domain and the same nonzero modulus, whose parameters multiply to the image of that modulus, the modulus being a unit times $\pi^{w(e)}$; attachment data $\mathrm{An}(e)$ attached to $C_{\mathrm{src}(e)}$ at the node $x_s(e)$ and $\mathrm{An}'(e)$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; the requirement that every node of every chart is an endpoint of an annulus and that the assignment $\mathrm{Fin}\ m \oplus \mathrm{Fin}\ m \to \coprod_j \mathrm{Place}\ \kappa\ \bar F_j$, $e \mapsto (\mathrm{src}(e), x_s(e))$ resp. $(\mathrm{tgt}(e), x_t(e))$, hits each node at most once; the covering condition that each place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; a disc-fibre condition providing, for each $i$ and each non-node place $Q$ of $\bar F_i$, a chart-integral $T$ whose residue is nonzero with $\mathrm{ord}_Q = 1$, which is regular with value in the maximal ideal of $A$ at every chart place above $Q$ and whose value realises each element of the maximal ideal at exactly one such place; and the genus identity $g(F/L) + n = \sum_i g(\bar F_i/\kappa) + m + 1$. Then for every divisor $D$ of $F/L$ there exist $\ell(D) = \dim_L \mathrm{riemannRochSpace}\ D$ elements $s_j \in F$, each lying in $\mathcal O_i$ for every $i$, each lying in the Riemann–Roch space of $D$ (i.e. $v(s_j) \le \exp(D(v))$ for every place $v$ of $F/L$), such that the $\ell(D)$ tuples of residues $j \mapsto (C_i.\mathrm{residue}(s_j))_{i}$ in $\prod_i \bar F_i$ are linearly independent over $\kappa$.
--
--   This is the form, for a semistable covering with finitely many component charts at once, of the classical statement of constant reduction theory that reduction does not lower the dimension of a linear system: the $\ell(D)$-dimensional space $L(D)$ admits a basis of functions integral on all charts whose reduction tuples remain $\kappa$-independent. It is used in the construction of functions on $F$ with prescribed residues on the components, namely by [`AlgebraicCurve.SemistableCovering.exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne) and [`AlgebraicCurve.SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_mem_riemannRochSpace_forall_residue_eq_of_glued_of_rankOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.exists_linearIndependent_pi_residue_of_mem_riemannRochSpace_of_rankOne
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
    (D : Divisor L F)
    :
    ∃ s : Fin (Module.finrank L (riemannRochSpace D)) → F,
      ∃ hs : ∀ j i, s j ∈ (C i).integers,
        (∀ j, s j ∈ riemannRochSpace D) ∧
        LinearIndependent (IsLocalRing.ResidueField A) (fun j => fun i => (C i).residue ⟨s j, hs j i⟩) := by sorry
