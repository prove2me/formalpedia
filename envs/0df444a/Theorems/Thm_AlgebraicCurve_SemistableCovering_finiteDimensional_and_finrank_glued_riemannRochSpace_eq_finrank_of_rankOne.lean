-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
-- name    : AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/32267d50-a642-573a-90da-3815a1a5cdf4
-- title:
--   Dimension of glued Riemann–Roch spaces on a semistable covering
-- statement:
--   Let $L$ be an algebraically closed field and $A\subseteq L$ a valuation subring with maximal ideal $\mathfrak m_A$ and residue field $\kappa$; fix $\pi\in\mathfrak m_A$ with $\pi\neq 0$, and assume $A$ has rank one in the form: for every $x\in L^\times$ and every $y\in\mathfrak m_A$ there is $n$ with $v_A(y^n)\le v_A(x)$. Let $F$ be a field extension of $L$, let $n,m\in\mathbb N$, and let $\bar F_0,\dots,\bar F_{n-1}$ be fields over $\kappa$ all of whose places (in the project's sense: valuation subrings containing $\kappa$, proper, with principal ideals) are rational, i.e. $\kappa$ surjects onto their residue fields. For each $i$ let $C_i$ be a component chart of $F$ along $A$ with values in $\bar F_i$: a valuation subring of $F$ with a surjective residue map onto $\bar F_i$ whose kernel is the maximal ideal, a set $\mathrm{dom}(C_i)$ of places of $F/L$, a finite set $\mathrm{nodes}(C_i)$ of places of $\bar F_i/\kappa$, a reduction map $\mathrm{placeMap}$ on places, together with the compatibility axioms of that structure; assume every place in $\mathrm{dom}(C_i)$ is rational. Let $\mathrm{An}_e,\mathrm{An}'_e$ ($e<m$) be annuli of $F$ along $A$ (a set of places, a parameter in $F$, a modulus in $\mathfrak m_A$, and the axioms on evaluation of the parameter, on order of $\mathrm{param}-\mathrm{evalAt}(\mathrm{param})$ and the unit principle), with $\mathrm{src},\mathrm{tgt}:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, node places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$, $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and weights $w(e)\in\mathbb N$ subject to: $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that modulus is nonzero in $L$ and is a unit times $\pi^{w(e)}$, and the product of the two parameters is the image of the modulus; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ (so each $x$ is a node, the parameter lies in the chart's integers with residue of order $1$ at $x$, and the stated unit comparison holds); every node of every chart is an end $(\mathrm{src}(e),x_s(e))$ or $(\mathrm{tgt}(e),x_t(e))$ of an annulus, and for exactly one such end; every place of $F/L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; and the disc-fibre condition: for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the integers of $C_i$ whose residue is nonzero with $\mathrm{ord}_Q$ equal to $1$, which lies in the valuation ring of every $P\in\mathrm{dom}(C_i)$ above $Q$ with $\mathrm{evalAt}_P(T)\in\mathfrak m_A$, and such that every $c\in\mathfrak m_A$ is $\mathrm{evalAt}_P(T)$ for a unique such $P$. Assume the genus identity $g(F/L)+n=\sum_i g(\bar F_i/\kappa)+m+1$, that $F$ is a curve over $L$ and each $\bar F_i$ a curve over $\kappa$ (principal divisors, finite residue extensions, one-dimensional free module of differentials), both essentially of finite type. Finally let $D$ be a divisor of $F/L$ supported in the union of the chart domains such that, writing $\bar D_i$ for the push-forward under $\mathrm{placeMap}$ of the part of $D$ supported in $\mathrm{dom}(C_i)$, one has $2g(\bar F_i)-1+\#\mathrm{nodes}(C_i)\le\deg \bar D_i$ for every $i$. Then the $\kappa$-subspace of $\prod_i \bar F_i$ spanned by the tuples $(h_i)$ with $h_i$ in the Riemann–Roch space of $\bar D_i$ (i.e. $v(h_i)\le \exp(\bar D_i(v))$ for all places $v$) and with $x_s(e)(h_{\mathrm{src}(e)})=x_t(e)(h_{\mathrm{tgt}(e)})$ for every $e$ is finite-dimensional over $\kappa$, and its $\kappa$-dimension equals the $L$-dimension of the Riemann–Roch space of $D$.
--
--   This is the dimension count underlying Deuring-style reduction of a function field with semistable reduction: the glued spaces of reductions of sections, with matching values at the nodes, have the same dimension as the Riemann–Roch space upstairs, the genus identity and the degree bounds making the $m$ gluing conditions independent. It is used by [`AlgebraicCurve.SemistableCovering.exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne`](thm.html#AlgebraicCurve.SemistableCovering.exists_forall_residue_eq_of_forall_evalAt_eq_of_discFibres_of_rankOne), where a span of tuples of residues of functions on $F$ is compared with this glued space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical in

theorem AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_glued_riemannRochSpace_eq_finrank_of_rankOne
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
    (hdegD : ∀ i, 2 * (genusFF (IsLocalRing.ResidueField A) (Fbar i) : ℤ) - 1 + ((C i).nodes.card : ℤ) ≤
      Divisor.degree (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
        Divisor (IsLocalRing.ResidueField A) (Fbar i)))
    :
    FiniteDimensional (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
              Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
            ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))}) ∧
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Finsupp.mapDomain (C i).placeMap (D.filter fun P => P ∈ (C i).dom) :
              Divisor (IsLocalRing.ResidueField A) (Fbar i))) ∧
            ∀ e, (xs e).evalAt (h (src e)) = (xt e).evalAt (h (tgt e))}) =
      Module.finrank L (riemannRochSpace D) := by sorry
