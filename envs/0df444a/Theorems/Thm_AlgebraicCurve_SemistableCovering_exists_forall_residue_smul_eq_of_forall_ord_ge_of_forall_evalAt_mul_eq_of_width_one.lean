-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
-- name    : AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/637eb8d7-48f5-56d9-a1f9-8bc440781697
-- title:
--   Graded Deuring lifting on a width-one semistable covering
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $\pi$ a nonzero element of the maximal ideal of $A$, with $A$ of rank one in the sense that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors exist with degree $0$, residue fields finite over $L$, $\Omega_{F/L}$ free of rank one) and essentially of finite type, and let $\bar F_i$, $i \in \mathrm{Fin}\,n$, be fields over the residue field $k = A/\mathfrak m_A$, each a curve over $k$, essentially of finite type, all of whose places are rational. Data: component charts $C_i$ (a valuation subring $(C_i).\mathrm{integers}$ of $F$ with surjective residue map onto $\bar F_i$ with kernel the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$ consisting of rational places, a finite set of nodes in $\bar F_i$, and a map $(C_i).\mathrm{placeMap}$ on places); annuli $An_e, An'_e$, $e \in \mathrm{Fin}\,m$, with ends $xs_e$ on $\bar F_{src\,e}$ and $xt_e$ on $\bar F_{tgt\,e}$; and widths $w_e$. The hypotheses are: $An'_e$ and $An_e$ have the same domain and the same (nonzero) modulus, the product of their parameters being the image of that modulus ($hpair$); each modulus is $u_e\pi^{w_e}$ with $u_e \in A^{\times}$, and $w_e = 1$; $An_e$ is attached to $C_{src\,e}$ at $xs_e$ and $An'_e$ to $C_{tgt\,e}$ at $xt_e$ (each end a node, the parameter integral with residue of order $1$ there, together with the unit comparison property in `IsAttached`); every node of every chart is an end of some annulus, and no two of the $2m$ ends coincide; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; the disc-fibre condition: for each non-node place $Q$ of $\bar F_i$ there is $T$ in $(C_i).\mathrm{integers}$ whose residue is nonzero of order $1$ at $Q$, such that $T$ lies in the valuation subring of every $P \in (C_i).\mathrm{dom}$ over $Q$ with $P.\mathrm{evalAt}\,T$ in $\mathfrak m_A$, and such that each $c \in \mathfrak m_A$ is the value $P.\mathrm{evalAt}\,T$ of a unique such $P$; and the genus identity $g(F/L) + n = \sum_i g(\bar F_i/k) + m + 1$. Finally let $\varphi : \mathrm{Fin}\,n \to \mathbb Z$ and let $D$ be a divisor of $F/L$ supported in the chart domains, with $2g(\bar F_i) - 1 + \#\mathrm{nodes}(C_i) \le \deg \bar D_i + \sum_e \big((\varphi(i) - \varphi(tgt\,e))[src\,e = i] + (\varphi(i) - \varphi(src\,e))[tgt\,e = i]\big)$ for every $i$, where $\bar D_i$ is the push-forward along $(C_i).\mathrm{placeMap}$ of the part of $D$ in $(C_i).\mathrm{dom}$. Put $k_e = \varphi(tgt\,e) - \varphi(src\,e)$, let $zs_e \in \bar F_{src\,e}$, $zt_e \in \bar F_{tgt\,e}$ be the residues of the parameters of $An_e$, $An'_e$, let $\bar u_e \in k$ be the residue of $u_e$, and $wt_i = (\pi^{\varphi(i)})^{-1} \in L$. The conclusion is two-part. First, for every $g \in F$ with $wt_i \cdot g$ integral on every chart, $g \ne 0$ and $\mathrm{div}(g) + D \ge 0$, the reductions $h_i = \overline{wt_i \cdot g} \in \bar F_i$ satisfy $\mathrm{ord}_Q h_i + \bar D_i(Q) \ge 0$ at every non-node $Q$ with $h_i \ne 0$, $\mathrm{ord}_{xs_e} h_{src\,e} \ge k_e$ and $\mathrm{ord}_{xt_e} h_{tgt\,e} \ge -k_e$ whenever the relevant reduction is nonzero, and the matching relation $xs_e.\mathrm{evalAt}(h_{src\,e} \, zs_e^{-k_e}) \cdot \bar u_e^{\,k_e} = xt_e.\mathrm{evalAt}(h_{tgt\,e} \, zt_e^{k_e})$ for every $e$. Second, conversely, every tuple $(h_i)_i$ satisfying these four conditions arises in this way: there is $g \in F$ with $wt_i \cdot g$ integral on every chart, with $g = 0$ or $\mathrm{div}(g) + D \ge 0$, and with $\overline{wt_i \cdot g} = h_i$ for all $i$.
--
--   This is the graded form of Deuring's reduction theorem for a function field covered, over a rank-one valuation subring, by component charts and annuli of width one: the chart-by-chart reduction map on the Riemann–Roch space of $D$ lands in, and surjects onto, the space of tuples of component functions with the pole bounds $\bar D_i$, the slope conditions $\pm k_e$ at the annulus ends dictated by the potential $\varphi$, and the leading-coefficient matching across each annulus. It is used in the construction of functions realising prescribed chip-firing moves on the dual graph of a semistable covering, namely by [`AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one`](thm.html#AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

open Classical in

theorem AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one
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
    (hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)) +
      ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0)))
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
        (xt e).evalAt ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩ * zt e ^ (k e))) ∧

    (∀ h : ∀ i, Fbar i,
      (∀ i, ∀ Q, Q ∉ (C i).nodes → h i ≠ 0 → 0 ≤ Q.ord (h i) + Dbar i Q) →
      (∀ e, h (src e) ≠ 0 → k e ≤ (xs e).ord (h (src e))) →
      (∀ e, h (tgt e) ≠ 0 → -k e ≤ (xt e).ord (h (tgt e))) →
      (∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))) →
      ∃ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers), (g = 0 ∨ ∀ P, 0 ≤ P.ord g + D P) ∧
        ∀ i, (C i).residue ⟨wt i • g, hg i⟩ = h i) := by sorry
