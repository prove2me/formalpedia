-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
-- name    : AlgebraicCurve.SemistableCovering.ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/89db9c02-5f75-5b93-a0ea-c8ed1341e5a1
-- title:
--   Graded reductions on a width-one semistable covering are compatible
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring with a nonzero element $\pi$ of its maximal ideal, such that for every $x\in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$ (rank one). Let $F/L$ be a field extension, a curve over $L$ in the sense of `IsCurveOver` and essentially of finite type, and let $\bar F_1,\dots,\bar F_n$ be curves over the residue field $k=A/\mathfrak m_A$, essentially of finite type, all of whose places are rational, equipped with component charts $C_i=(\,$a valuation subring of $F$ with residue map onto $\bar F_i$, a set $\mathrm{dom}$ of places of $F/L$ all of which are rational, a finite set of nodes in $\bar F_i$, and a map $\mathrm{placeMap}$ to places of $\bar F_i$, with the axioms of `ComponentChart`$\,)$. Let $An_e,An'_e$ ($e\in\{1,\dots,m\}$) be annuli over $A$ with given source and target indices $\mathrm{src}(e),\mathrm{tgt}(e)$ and node places $xs_e\in\bar F_{\mathrm{src}(e)}$, $xt_e\in\bar F_{\mathrm{tgt}(e)}$, and widths $w_e\in\mathbb N$, subject to: $An'_e$ and $An_e$ have the same domain and the same modulus, that modulus is nonzero in $L$ and is the product of the two parameters (under $L\to F$); the modulus equals $u_e\pi^{w_e}$ for some unit $u_e$ of $A$; $w_e=1$ for all $e$; $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $xs_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $xt_e$; every node of every chart is the end of at least one annulus end, and the map from annulus ends (a disjoint union of two copies of the index set, sources and targets) to marked nodes is injective; every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; a disc-fibre condition at every non-node place $Q$ of every $\bar F_i$ (existence of an integral $T$ with nonvanishing residue of valuation $1$ at $Q$, lying in every place of the fibre with value in $\mathfrak m_A$, and with $T$ parametrising that fibre bijectively by $\mathfrak m_A$); and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/k)+m+1$. Fix $\varphi\colon\{1,\dots,n\}\to\mathbb Z$ and a divisor $D$ of $F/L$ supported in the union of the chart domains; put $\bar D_i$ for the push-forward along $\mathrm{placeMap}$ of the part of $D$ in $\mathrm{dom}(C_i)$, $k_e=\varphi(\mathrm{tgt}(e))-\varphi(\mathrm{src}(e))$, $zs_e$ and $zt_e$ for the residues in $\bar F_{\mathrm{src}(e)}$, $\bar F_{\mathrm{tgt}(e)}$ of the parameters of $An_e$, $An'_e$, $\bar u_e\in k$ for the residue of the chosen unit $u_e$, and $wt_i=(\pi^{\varphi(i)})^{-1}\in L$. The conclusion: for every $g\in F$ with $wt_i\cdot g$ integral on every chart, say with residues $h_i\in\bar F_i$, if $g\neq 0$ and $\operatorname{ord}_P(g)+D(P)\ge 0$ for every place $P$, then (i) $\operatorname{ord}_Q(h_i)+\bar D_i(Q)\ge 0$ for every $i$ and every non-node $Q$ with $h_i\neq0$; (ii) $\operatorname{ord}_{xs_e}(h_{\mathrm{src}(e)})\ge k_e$ whenever $h_{\mathrm{src}(e)}\neq0$; (iii) $\operatorname{ord}_{xt_e}(h_{\mathrm{tgt}(e)})\ge -k_e$ whenever $h_{\mathrm{tgt}(e)}\neq0$; and (iv) for every $e$, the evaluation at the rational place $xs_e$ of $h_{\mathrm{src}(e)}\,zs_e^{-k_e}$, multiplied by $\bar u_e^{\,k_e}$, equals the evaluation at $xt_e$ of $h_{\mathrm{tgt}(e)}\,zt_e^{\,k_e}$, where evaluation is the residue-inverse map into $k$, set to $0$ off the valuation subring.
--
--   This is the constant-reduction (Deuring) bookkeeping for a semistable covering of a curve by component charts glued along annuli of width one: a function with bounded poles and prescribed $\pi$-scaling $\varphi$ on the charts has reductions whose pole orders on the components are bounded by the pushed-forward divisor, whose orders at the nodes are bounded by the slopes $k_e$ of $\varphi$ along the annuli, and whose leading coefficients at the two ends of each annulus agree up to the residue of the modulus unit. It is the input to [`AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one`](thm.html#AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one), the converse lifting statement, and the annulus-by-annulus comparison is supplied by [`AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached`](thm.html#AlgebraicCurve.Annulus.ord_residue_nonneg_and_evalAt_residue_eq_of_isAttached_of_isAttached).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

open Classical in

theorem AlgebraicCurve.SemistableCovering.ord_residue_smul_ge_and_evalAt_mul_eq_of_forall_smul_mem_integers_of_width_one
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
    (hw1 : ∀ e, w e = 1)
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
    (φ : Fin n → ℤ)
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    :
    let Dbar : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom)
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let zs : ∀ e, Fbar (src e) := fun e => (C (src e)).residue ⟨(An e).param, (hatt e).1.2.choose⟩
    let zt : ∀ e, Fbar (tgt e) := fun e => (C (tgt e)).residue ⟨(An' e).param, (hatt e).2.2.choose⟩
    let ubar : Fin m → IsLocalRing.ResidueField A := fun e => IsLocalRing.residue A ((hw e).choose : A)
    let wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹

    (∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), g ≠ 0 → (∀ P, 0 ≤ P.ord g + D P) →
      (∀ i, ∀ Q, Q ∉ (C i).nodes → (C i).residue ⟨wt i • g, hg i⟩ ≠ 0 →
        0 ≤ Q.ord ((C i).residue ⟨wt i • g, hg i⟩) + Dbar i Q) ∧
      (∀ e, (C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ ≠ 0 →
        k e ≤ (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩)) ∧
      (∀ e, (C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ ≠ 0 →
        -k e ≤ (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩)) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩ * zs e ^ (-k e)) * ubar e ^ (k e) =
        (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e))) := by sorry
