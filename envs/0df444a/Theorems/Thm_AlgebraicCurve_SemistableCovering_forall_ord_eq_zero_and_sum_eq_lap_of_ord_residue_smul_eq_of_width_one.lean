-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
-- name    : AlgebraicCurve.SemistableCovering.forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/36003885-07cb-5e9b-967a-444f94b3b62b
-- title:
--   No zeros on width-one annuli; Laplacian chart degrees
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, $\pi\in A$ a nonzero element of the maximal ideal, and assume the rank-one condition that for every $x\in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (nonzero elements have finitely supported degree-zero principal divisors, places have residue fields finite over $L$, and $\Omega[F/L]$ is free of rank one) and essentially of finite type, and let $\bar F_i$, $i\in\mathrm{Fin}\,n$, be curves over $\kappa=\mathrm{ResidueField}(A)$, essentially of finite type, all of whose places are rational (the map from $\kappa$ to the residue field is surjective). Given component charts $C_i$ over $A$ with target $\bar F_i$, all places of $(C_i).\mathrm{dom}$ rational, annuli $\mathrm{An}_e,\mathrm{An}'_e$ for $e\in\mathrm{Fin}\,m$ with maps $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, nodes $x^{s}_e$ on $\bar F_{\mathrm{src}\,e}$, $x^{t}_e$ on $\bar F_{\mathrm{tgt}\,e}$, and widths $w_e$, assume: $\mathrm{An}'_e$ has the same domain and modulus as $\mathrm{An}_e$, this modulus is nonzero in $L$ and equals the product of the two parameters; each modulus is a unit times $\pi^{w_e}$ with $w_e=1$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x^{s}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x^{t}_e$ (the node lies in the chart's nodes, the annulus parameter lies in the chart's integers with residue of order one at the node, and the unit-representative law for functions without zeros on the annulus holds); every node of every chart is an endpoint of some annulus, and distinct ends of annuli give distinct nodes; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in $(C_i).\mathrm{integers}$ whose residue is nonzero of order one at $Q$, integral with $\mathrm{evalAt}$ in the maximal ideal at every place of the chart domain above $Q$, and such that every $c$ in the maximal ideal of $A$ is the value $P.\mathrm{evalAt}\,T$ of a unique place $P$ of the chart domain above $Q$; and the genus relation $\mathrm{genus}(F/L)+n=\sum_i\mathrm{genus}(\bar F_i/\kappa)+m+1$. Fix $\varphi:\mathrm{Fin}\,n\to\mathbb{Z}$, put $k_e=\varphi(\mathrm{tgt}\,e)-\varphi(\mathrm{src}\,e)$ and $\mathrm{wt}_i=(\pi^{\varphi(i)})^{-1}\in L$. Then for every $g\in F$ with $\mathrm{wt}_i\cdot g\in (C_i).\mathrm{integers}$ for all $i$, such that each residue $(C_i).\mathrm{residue}(\mathrm{wt}_i\cdot g)$ is nonzero, $P.\mathrm{ord}\,g\ge 0$ at every place of every annulus domain, and the node orders are exactly $k_e$ at $x^{s}_e$ and $-k_e$ at $x^{t}_e$: first, $P.\mathrm{ord}\,g=0$ for every place $P$ in every annulus domain; second, for every $i$ and every divisor $D_g$ on $F/L$ agreeing with $P\mapsto P.\mathrm{ord}\,g$ on $(C_i).\mathrm{dom}$ and vanishing off it, the sum of the values of $D_g$ equals $\sum_e\big(\,[\mathrm{src}\,e=i](\varphi(i)-\varphi(\mathrm{tgt}\,e))+[\mathrm{tgt}\,e=i](\varphi(i)-\varphi(\mathrm{src}\,e))\,\big)$.
--
--   This is the exactness step in the lifting of functions along a semistable covering by width-one annuli: under the stated node-order conditions the lift has no zero or pole on any annulus, and its degree on each chart is the graph Laplacian of the potential $\varphi$ at the corresponding vertex. It feeds [`AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one`](thm.html#AlgebraicCurve.exists_ne_zero_apply_ord_eq_sum_lap_of_semistableCovering_of_discFibres_of_rankOne_of_width_one), where a function with prescribed Laplacian divisor is produced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.SemistableCovering.forall_ord_eq_zero_and_sum_eq_lap_of_ord_residue_smul_eq_of_width_one
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
    :
    let k : Fin m → ℤ := fun e => φ (tgt e) - φ (src e)
    let wt : Fin n → L := fun i => (((π : A) : L) ^ (φ i))⁻¹
    ∀ (g : F) (hg : ∀ i, wt i • g ∈ (C i).integers),
      (∀ i, (C i).residue ⟨wt i • g, hg i⟩ ≠ 0) →
      (∀ e, ∀ P ∈ (An e).dom, 0 ≤ P.ord g) →
      (∀ e, (xs e).ord ((C (src e)).residue ⟨wt (src e) • g, hg (src e)⟩) = k e) →
      (∀ e, (xt e).ord ((C (tgt e)).residue ⟨wt (tgt e) • g, hg (tgt e)⟩) = -k e) →

      (∀ e, ∀ P ∈ (An e).dom, P.ord g = 0) ∧

      (∀ i (Dg : Divisor L F), (∀ P ∈ (C i).dom, Dg P = P.ord g) → (∀ P, P ∉ (C i).dom → Dg P = 0) →
        (Dg.sum fun _ l => l) =
          ∑ e, ((if src e = i then φ i - φ (tgt e) else 0) + (if tgt e = i then φ i - φ (src e) else 0))) := by sorry
