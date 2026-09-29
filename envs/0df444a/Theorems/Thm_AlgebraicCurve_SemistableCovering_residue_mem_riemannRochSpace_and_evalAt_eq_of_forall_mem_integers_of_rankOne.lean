-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/f5f44633-e1f3-55ef-9441-1dde967285e2
-- title:
--   Chart reductions of a Riemann–Roch function match along the annuli
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring with maximal ideal $\mathfrak m_A$, and $\pi\in\mathfrak m_A$ nonzero; assume the rank-one condition that for every nonzero $x\in L$ and every $y\in\mathfrak m_A$ some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$, and let $n,m$ be naturals, $\bar F_i$ ($i\in\mathrm{Fin}\,n$) fields over the residue field $\kappa=A/\mathfrak m_A$ all of whose places (valuation subrings, non-trivial, with principal ideal rings of integers, containing the base field) are rational, i.e. $\kappa$ maps onto their residue fields. Given component charts $C_i$ of $F$ over $A$ with values in $\bar F_i$ (a valuation subring $(C_i).\mathrm{integers}$ of $F$ with surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$, all rational, a finite set of nodes in the places of $\bar F_i/\kappa$, and a place map $(C_i).\mathrm{placeMap}$, subject to the compatibility, pointwise-evaluation and divisor-push-forward axioms of the structure), annuli $\mathrm{An}(e),\mathrm{An}'(e)$ ($e\in\mathrm{Fin}\,m$) with source and target indices $\mathrm{src}(e),\mathrm{tgt}(e)$ and nodes $x_s(e),x_t(e)$, and weights $w(e)$, assume: each pair $\mathrm{An}'(e),\mathrm{An}(e)$ has the same domain and the same nonzero modulus $\mu_e$, with $\mathrm{An}'(e).\mathrm{param}\cdot\mathrm{An}(e).\mathrm{param}=\mu_e$; $\mu_e$ is a unit times $\pi^{w(e)}$; $\mathrm{An}(e)$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'(e)$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; every node of every $C_i$ is an end of some annulus, and of exactly one end, as a condition on the map $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m\to\Sigma_j\,\mathrm{Place}(\kappa,\bar F_j)$; every place of $F/L$ lies in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is a disc parameter $T\in (C_i).\mathrm{integers}$ whose reduction is nonzero with $\mathrm{ord}_Q=1$, which is integral with value in $\mathfrak m_A$ at all places of $(C_i).\mathrm{dom}$ above $Q$, and such that each $c\in\mathfrak m_A$ is the value of $T$ at a unique such place; and the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$, where $g$ is the dimension of $H^1$ of the zero divisor. Assume further that $F/L$ and every $\bar F_i/\kappa$ is a curve (principal divisors of degree zero, finite residue extensions, and module of Kähler differentials free of rank one) and essentially of finite type. Finally let $D$ be a divisor of $F/L$ supported in the union of the chart domains. Then for every nonzero $f\in F$ lying in $(C_i).\mathrm{integers}$ for all $i$ and lying in the Riemann–Roch space of $D$ (at each place the adic valuation of $f$ is at most $\exp(D(v))$): the reduction of $f$ in $\bar F_i$ lies in the Riemann–Roch space of the push-forward along $(C_i).\mathrm{placeMap}$ of the restriction of $D$ to $(C_i).\mathrm{dom}$, for every $i$; and for every $e$ the value at $x_s(e)$ of the reduction of $f$ in $\bar F_{\mathrm{src}(e)}$ equals the value at $x_t(e)$ of the reduction of $f$ in $\bar F_{\mathrm{tgt}(e)}$, values being taken through the inverse of $\kappa\to$ residue field of the place.
--
--   This is the descent half of Deuring-style constant reduction for a semistable covering: functions with prescribed poles on $F$ reduce to sections of the push-forward divisors on the components, subject to the matching conditions at the nodes. It is used in the comparison of the Riemann–Roch space of $D$ with the space of matching tuples of sections on the components, its consumer being the statement producing a function with prescribed chart reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical in

theorem AlgebraicCurve.SemistableCovering.residue_mem_riemannRochSpace_and_evalAt_eq_of_forall_mem_integers_of_rankOne
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
    (D : Divisor L F) (hD : ∀ P ∈ D.support, ∃ i, P ∈ (C i).dom)
    :
    ∀ (f : F) (hf : ∀ i, f ∈ (C i).integers), f ≠ 0 → f ∈ riemannRochSpace D →
      (∀ i, (C i).residue ⟨f, hf i⟩ ∈
        riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
          Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
      ∀ e, (xs e).evalAt ((C (src e)).residue ⟨f, hf (src e)⟩) = (xt e).evalAt ((C (tgt e)).residue ⟨f, hf (tgt e)⟩) := by sorry
