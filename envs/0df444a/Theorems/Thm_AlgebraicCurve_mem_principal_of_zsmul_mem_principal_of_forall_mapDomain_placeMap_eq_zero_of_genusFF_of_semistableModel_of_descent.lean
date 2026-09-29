-- Prove2me | Theorems.Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
-- name    : AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/eae715f0-70ef-5b6b-9559-3f56ac2aa42d
-- title:
--   Divisibility descent for chart-supported divisors on a semistable model
-- statement:
--   Let $L$ be an algebraically closed field and $A$ a valuation subring of $L$, with $\pi$ a nonzero element of its maximal ideal and satisfying the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$; write $\kappa$ for the residue field of $A$. Let $F/L$ be an extension which is a curve over $L$ (every place has finite residue extension over $L$ and $\Omega_{F/L}$ is free of rank one) and essentially of finite type. The combinatorial data are finite index sets $\iota V$, $\iota E$; fields $\bar F_i/\kappa$, each a curve over $\kappa$ and essentially of finite type, all of whose places are rational (the structure map to the residue field of a place is surjective); component charts $C_i$ over $A$ (a valuation subring of $F$ of $\text{integers}$ with surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, a set $\mathrm{dom}$ of places of $F/L$, all of them rational, a finset of nodes in $\bar F_i$, and a reduction map $\text{placeMap}$); two families of annuli $\mathrm{An}_e$, $\mathrm{An}'_e$ with source and target maps $\mathrm{src},\mathrm{tgt} : \iota E \to \iota V$, node places $x^{s}_e$ on $\bar F_{\mathrm{src}(e)}$ and $x^{t}_e$ on $\bar F_{\mathrm{tgt}(e)}$, and weights $w_e \in \mathbb{N}$. The hypotheses on these data are: each pair $(\mathrm{An}_e,\mathrm{An}'_e)$ has the same domain and the same modulus, that modulus is nonzero in $L$, and the product of the two parameters is the image of the modulus; each modulus equals a unit of $A$ times $\pi^{w_e}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{t}_e$; every node of every chart is an endpoint of some edge-end and of exactly one (uniqueness over $\iota E \oplus \iota E$); every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; at each non-node place $Q$ of $\bar F_i$ there is a function $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q = 1$, which is integral at every place of $\mathrm{dom}$ reducing to $Q$ with value in the maximal ideal there, and such that every $c$ in the maximal ideal of $A$ is the value of $T$ at exactly one place of $\mathrm{dom}$ above $Q$; and the genus identity $g(F/L) + \#\iota V = \sum_i g(\bar F_i/\kappa) + \#\iota E + 1$, genus being the $\kappa$- respectively $L$-dimension of $H^{1}$ of the zero divisor. Given in addition a semistable model $M$ for these data and a descent datum $D$ for $M$, a natural number $k$ whose image in $\kappa$ is a unit, divisors $G_i$ on $F/L$ supported in $\mathrm{dom}\,C_i$ with $\text{placeMap}$-pushforward zero, a finite set $\iota$, edges $e_j$, integers $n_j$ and quadruples $Q_{j0},\dots,Q_{j3}$ of places in $\mathrm{An}_{e_j}.\mathrm{dom}$ such that the values of the parameter satisfy $Q_{j0}(\text{param}) = u \cdot Q_{j2}(\text{param})$ for some unit $u$ of $A$ and the balance relation $Q_{j0}(\text{param}) \, Q_{j1}(\text{param}) = Q_{j2}(\text{param}) \, Q_{j3}(\text{param})(1+t)$ for some $t$ in the maximal ideal: if $k$ times the divisor $G = \sum_i G_i + \sum_j n_j((Q_{j0}) + (Q_{j1}) - (Q_{j2}) - (Q_{j3}))$ is principal, that is of the form $v \mapsto v.\mathrm{ord}(f)$ for some $f \neq 0$, then $G$ itself is principal.
--
--   This is the arithmetic form of the statement that a divisor supported on the charts and annuli of a semistable covering, with vanishing reductions on each component and balanced annulus quadruples, is principal as soon as a multiple of it by an integer invertible in the residue characteristic is principal; the proof goes through Cartier data on the model, the associated $\mu_k$-Kummer cover, and section lifting after finite descent to a noetherian henselian base. It is used by the covering-level version of the same divisibility statement and by the constructions of Tate modules and of kernel elements for semistable coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent
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
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (Gi : ιV → Divisor L F) (hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0)
    {ι : Type*} [Fintype ι] (e : ι → ιE) (nq : ι → ℤ) (Q : ι → Fin 4 → Place L F)
    (hQ : ∀ j l, Q j l ∈ (An (e j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
        (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L)))
    (hkG : (k : ℤ) • (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
        - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
      Divisor.principal (K := L) (F := F)) :
    (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
        - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) ∈
      Divisor.principal (K := L) (F := F) := by sorry
