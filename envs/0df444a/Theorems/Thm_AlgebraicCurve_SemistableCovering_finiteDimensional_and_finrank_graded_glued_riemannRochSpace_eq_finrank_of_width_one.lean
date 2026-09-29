-- Prove2me | Theorems.Thm_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
-- name    : AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.078526+00:00
-- url     : https://prove2.me/theorems/1bd4adad-f795-5617-8e25-4532adc92608
-- title:
--   Dimension of the graded glued Riemann–Roch space equals ℓ(D)
-- statement:
--   Let $L$ be an algebraically closed field and $A \subseteq L$ a valuation subring, with $\pi$ a nonzero element of its maximal ideal, and assume $A$ has rank one in the sense that for every $x \in L^\times$ and every $y$ in the maximal ideal of $A$ some power $y^n$ has valuation at most that of $x$. Let $F$ be a field extension of $L$, let $n, m \in \mathbb{N}$, and for $i \in \mathrm{Fin}\,n$ let $\bar F_i$ be a field extension of $\kappa =$ the residue field of $A$, all of whose places over $\kappa$ are rational (i.e. $\kappa$ surjects onto their residue fields), together with a `ComponentChart` $C_i$ for $A$, $F$, $\bar F_i$ all of whose places in $(C_i).\mathrm{dom}$ are rational. Let $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) be annuli over $A$ in $F$, with $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and widths $w : \mathrm{Fin}\,m \to \mathbb{N}$, subject to: the two annuli of each $e$ have the same domain and the same modulus, that modulus is nonzero in $L$ and equals the product of the two parameters (via $L \to F$); the modulus is $u_e \pi^{w(e)}$ for a unit $u_e$ of $A$; $w(e) = 1$ for all $e$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$; every node of every chart is an end $\langle \mathrm{src}(e), x_s(e)\rangle$ or $\langle \mathrm{tgt}(e), x_t(e)\rangle$ of some annulus, and is such an end for exactly one element of $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$; every place of $F$ over $L$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; for each $i$ and each non-node place $Q$ of $\bar F_i$ there is $T$ in the valuation ring $(C_i).\mathrm{integers}$ whose residue is nonzero with $\mathrm{ord}_Q$ equal to $1$, such that every $P \in (C_i).\mathrm{dom}$ with $(C_i).\mathrm{placeMap}\,P = Q$ has $T$ in its valuation ring and $P.\mathrm{evalAt}\,T$ in the maximal ideal of $A$, and such that every $c$ in the maximal ideal of $A$ is $P.\mathrm{evalAt}\,T$ for a unique such $P$; and the genus identity $g(F/L) + n = \sum_i g(\bar F_i/\kappa) + m + 1$, where $g$ denotes `genusFF`. Assume moreover that $F$ is a curve over $L$ and each $\bar F_i$ a curve over $\kappa$, essentially of finite type. Finally let $\varphi : \mathrm{Fin}\,n \to \mathbb{Z}$, and let $D$ be a divisor of $F$ over $L$ whose support lies in the union of the chart domains and which satisfies, for every $i$, $$2g(\bar F_i/\kappa) - 1 + \#(C_i).\mathrm{nodes} \le \deg \bar D_i + \sum_e \bigl([\mathrm{src}(e) = i](\varphi(i) - \varphi(\mathrm{tgt}(e))) + [\mathrm{tgt}(e) = i](\varphi(i) - \varphi(\mathrm{src}(e)))\bigr),$$ where $\bar D_i$ is the push-forward along $(C_i).\mathrm{placeMap}$ of the part of $D$ supported in $(C_i).\mathrm{dom}$. Put $k_e = \varphi(\mathrm{tgt}(e)) - \varphi(\mathrm{src}(e))$, let $\bar z_s(e) \in \bar F_{\mathrm{src}(e)}$ and $\bar z_t(e) \in \bar F_{\mathrm{tgt}(e)}$ be the chart residues of the parameters of $\mathrm{An}_e$ and $\mathrm{An}'_e$ (which lie in the respective chart valuation rings by attachment), let $\bar u_e \in \kappa$ be the residue of the unit $u_e$, and let $K_i$ be the $i$-th component of the divisor-valued function $e \mapsto -k_e$ at $\langle \mathrm{src}(e), x_s(e)\rangle$ and $+k_e$ at $\langle \mathrm{tgt}(e), x_t(e)\rangle$, summed over $e$. Then the $\kappa$-span of the set of tuples $h = (h_i)_i \in \prod_i \bar F_i$ with $h_i \in \mathrm{riemannRochSpace}(\bar D_i + K_i)$ for all $i$ and $$x_s(e).\mathrm{evalAt}\bigl(h_{\mathrm{src}(e)} \bar z_s(e)^{-k_e}\bigr)\cdot \bar u_e^{\,k_e} = x_t(e).\mathrm{evalAt}\bigl(h_{\mathrm{tgt}(e)} \bar z_t(e)^{\,k_e}\bigr)$$ for all $e$ is a finite-dimensional $\kappa$-vector space, and its dimension equals $\dim_L \mathrm{riemannRochSpace}(D)$.
--
--   This is the counting half of the graded, potential-weighted form of Deuring's reduction theory for a semistable covering of $F$ by component charts glued along width-one annuli: the glued space of leading coefficients attached to the potential $\varphi$ has exactly the dimension $\ell(D)$ of the Riemann–Roch space upstairs. Together with the statements that graded reductions of $L(D)$ land in this glued space and that they remain independent, it supplies the surjectivity input for [`AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one`](thm.html#AlgebraicCurve.SemistableCovering.exists_forall_residue_smul_eq_of_forall_ord_ge_of_forall_evalAt_mul_eq_of_width_one); the case $\varphi \equiv 0$ is the ungraded count.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_SemistableCovering_finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical in

theorem AlgebraicCurve.SemistableCovering.finiteDimensional_and_finrank_graded_glued_riemannRochSpace_eq_finrank_of_width_one
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
    let Kdiv : ∀ i, Divisor (IsLocalRing.ResidueField A) (Fbar i) := fun i =>
      Finsupp.split (∑ e, (Finsupp.single (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) (-k e) +
        Finsupp.single (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) (k e))) i
    FiniteDimensional (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
            ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))}) ∧
    Module.finrank (IsLocalRing.ResidueField A)
        (Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fbar i |
            (∀ i, h i ∈ riemannRochSpace (Dbar i + Kdiv i)) ∧
            ∀ e, (xs e).evalAt (h (src e) * zs e ^ (-k e)) * ubar e ^ (k e) = (xt e).evalAt (h (tgt e) * zt e ^ (k e))}) =
      Module.finrank L (riemannRochSpace D) := by sorry
