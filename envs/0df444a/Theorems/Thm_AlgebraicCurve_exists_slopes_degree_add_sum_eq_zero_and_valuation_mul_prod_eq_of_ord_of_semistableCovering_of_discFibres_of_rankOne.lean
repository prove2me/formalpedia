-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
-- name    : AlgebraicCurve.exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/3a507ffb-3fba-545d-9190-9cb071b8d24e
-- title:
--   Slope formula for a function on a semistable covering
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; assume $A$ has rank one in the form that for every $x \in L^{\times}$ and every $y$ in the maximal ideal of $A$ some power satisfies $v_A(y^{n}) \le v_A(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ (principal divisors of degree zero, finite residue extensions at every place, and $\Omega_{F/L}$ free of rank one over $F$) and essentially of finite type. Let $n,m \in \mathbb{N}$, and for $i \in \mathrm{Fin}\,n$ let $\bar F_i$ be a field extension of the residue field $k$ of $A$, again a curve over $k$ and essentially of finite type, all of whose places are rational (the structure map to the residue field of the place is surjective). For each $i$ let $C_i$ be a component chart for $(A,F,\bar F_i)$ — a valuation subring of $F$ with a surjective residue map to $\bar F_i$ having the maximal ideal as kernel, a set $\mathrm{dom}(C_i)$ of places of $F/L$ all of which are assumed rational, a finite set $\mathrm{nodes}(C_i)$ of places of $\bar F_i/k$, and a reduction map on places, subject to the compatibility axioms of `ComponentChart`. For $e \in \mathrm{Fin}\,m$ let $\mathrm{An}_e$, $\mathrm{An}'_e$ be annuli (each a set of places together with a parameter and a modulus in the maximal ideal of $A$, subject to the axioms of `Annulus`), with $\mathrm{src}(e), \mathrm{tgt}(e)$ in $\mathrm{Fin}\,n$, places $x_s(e)$ of $\bar F_{\mathrm{src}(e)}$ and $x_t(e)$ of $\bar F_{\mathrm{tgt}(e)}$, and a weight $w(e) \in \mathbb{N}$. The hypotheses are: $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that modulus is nonzero in $L$ and the product of the two parameters is its image in $F$; the modulus of $\mathrm{An}_e$ is a unit times $\pi^{w(e)}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$ in the sense of `IsAttached`; every node of every chart is an endpoint of an edge, and the resulting map from $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$ to pairs (component, node) is injective onto each node; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; for every non-node place $Q$ of $\bar F_i$ there is a chart function $T$ with nonzero residue and $Q.\mathrm{ord}$ of that residue equal to $1$, integral with value in the maximal ideal of $A$ at every place of $\mathrm{dom}(C_i)$ reducing to $Q$, and such that each $c$ in the maximal ideal of $A$ is the value of $T$ at exactly one such place (a disc fibre over $Q$); and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/k) + m + 1$, where $g$ is the dimension of $H^1(0)$. Finally let $f \in F$ be nonzero, let $D_i$ be divisors of $F/L$ supported in $\mathrm{dom}(C_i)$ with $D_i(P) = P.\mathrm{ord}(f)$ there, and $N_e$ divisors supported in $\mathrm{dom}(\mathrm{An}_e)$ with $N_e(P) = P.\mathrm{ord}(f)$ there. The conclusion asserts the existence of slopes $\sigma : \mathrm{Fin}\,m \to \mathbb{Z}$ and nonzero scalings $a : \mathrm{Fin}\,n \to L$ such that, writing $\mathrm{mass}_e = \sum_P N_e(P)$, the vertex law $\deg D_i + \sum_{\mathrm{src}(e)=i} \sigma(e) + \sum_{\mathrm{tgt}(e)=i} (\mathrm{mass}_e - \sigma(e)) = 0$ holds for every $i$, and the edge law $$v_A(a(\mathrm{src}\,e)) \cdot \prod_P v_A\big(P.\mathrm{evalAt}(\mathrm{An}_e.\mathrm{param})\big)^{N_e(P)} = v_A(a(\mathrm{tgt}\,e)) \cdot v_A(\mathrm{An}_e.\mathrm{modulus})^{\,\mathrm{mass}_e - \sigma(e)}$$ holds for every $e$, where $P.\mathrm{evalAt}$ denotes the $L$-value of the residue at a rational place.
--
--   This is the slope formula (harmonicity of $-\log|f|$, or Poincaré–Lelong) for a semistable covering of the curve $F/L$: the restriction of $-\log|f|$ to the skeleton encoded by the charts $C_i$ and the annuli $\mathrm{An}_e$ is a tropical rational function whose divisor is the tropicalisation of $\operatorname{div} f$, the scaling $a_i$ normalising $f$ on the chart $i$. Unlike the special case with prescribed degree, mass and moment, no numerical hypothesis is imposed on the divisor of $f$; the statement is used in the analysis of chart-supported representatives for invariants of the rational Tate module of a semistable model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_slopes_degree_add_sum_eq_zero_and_valuation_mul_prod_eq_of_ord_of_semistableCovering_of_discFibres_of_rankOne
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
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
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f)
    :
    ∃ (σ : Fin m → ℤ) (a : Fin n → L), (∀ i, a i ≠ 0) ∧
      (∀ i : Fin n, Divisor.degree (Di i) + (∑ e, if src e = i then σ e else 0) +
          (∑ e, if tgt e = i then ((N e).sum fun _ k => k) - σ e else 0) = 0) ∧
      (∀ e : Fin m, A.valuation (a (src e)) * ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) =
          A.valuation (a (tgt e)) * A.valuation ((An e).modulus : L) ^ (((N e).sum fun _ k => k) - σ e)) := by sorry
