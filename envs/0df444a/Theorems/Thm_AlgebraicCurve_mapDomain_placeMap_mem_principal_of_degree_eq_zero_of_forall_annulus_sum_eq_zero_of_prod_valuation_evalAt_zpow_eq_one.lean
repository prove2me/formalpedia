-- Prove2me | Theorems.Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
-- name    : AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:41.617196+00:00
-- url     : https://prove2.me/theorems/718b6d0f-1dec-525a-bde6-79f1ba652500
-- title:
--   Slope formula: chart parts of div f are principal
-- statement:
--   Let $L$ be an algebraically closed field, $A\subseteq L$ a valuation subring, $\pi\in A$ an element of the maximal ideal with $\pi\neq 0$, and $F$ a field extension of $L$. Fix $n,m\in\mathbb N$ and, for each $i\in\mathrm{Fin}\,n$, a field $\bar F_i$ over the residue field $\kappa=\mathrm{ResidueField}\,A$ such that every nonzero element of $\bar F_i$ admits a finitely supported divisor equal to $\operatorname{ord}$ of it at every place and of degree $0$ (`HasPrincipalDivisors`), and such that every place $Q$ of $\bar F_i/\kappa$ is rational, i.e. $\kappa\to Q$'s residue field is surjective; fix component charts $C_i:\mathrm{ComponentChart}\,A\,F\,\bar F_i$, all places in $C_i.\mathrm{dom}$ being rational. Fix annuli $\mathrm{An}_e,\mathrm{An}'_e$ in $F$ over $A$ for $e\in\mathrm{Fin}\,m$, maps $s,t:\mathrm{Fin}\,m\to\mathrm{Fin}\,n$, places $x_s(e)$ of $\bar F_{s(e)}$ and $x_t(e)$ of $\bar F_{t(e)}$, and weights $w(e)\in\mathbb N$, subject to: $\mathrm{An}'_e$ and $\mathrm{An}_e$ have the same domain and the same modulus, that modulus is nonzero in $L$, and the product of the two parameters is the image in $F$ of the modulus; the modulus of $\mathrm{An}_e$ is $u\pi^{w(e)}$ for some unit $u\in A^\times$; $\mathrm{An}_e$ is attached to $C_{s(e)}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{t(e)}$ at $x_t(e)$ (so each such place is a node of the chart, the corresponding parameter lies in the chart's integers with residue of order $1$ at that node, and the chart's unit-slope condition holds); and each node $x$ of each $C_i$ is, as a pair $(i,x)$, the labelled endpoint $(s(e),x_s(e))$ or $(t(e),x_t(e))$ of at least one $e$, and any two elements of $\mathrm{Fin}\,m\oplus\mathrm{Fin}\,m$ giving the same labelled endpoint $(i,x)$ coincide. Let $f\in F$, $f\neq0$. For each $i$ let $D_i$ be a divisor on the places of $F/L$ supported inside $C_i.\mathrm{dom}$, with $D_i(P)=P.\operatorname{ord}f$ for $P\in C_i.\mathrm{dom}$ and $\deg D_i=0$; for each $e$ let $N_e$ be a divisor supported inside $\mathrm{An}_e.\mathrm{dom}$ with $N_e(P)=P.\operatorname{ord}f$ there, with $\sum_P N_e(P)=0$ and $\prod_P A.\mathrm{valuation}\bigl(P.\mathrm{evalAt}(\mathrm{An}_e.\mathrm{param})\bigr)^{N_e(P)}=1$. Then for every $i$ the pushforward $\mathrm{Finsupp.mapDomain}\,(C_i.\mathrm{placeMap})\,D_i$ is a principal divisor on $\bar F_i/\kappa$: there is a nonzero $g\in\bar F_i$ whose order at every place of $\bar F_i$ is the coefficient of that place in the pushforward.
--
--   This is the form of the slope formula (harmonicity of the tropicalisation of a rational function on a semistable curve) used here: if the chart parts of $\operatorname{div} f$ have degree zero and the annulus parts have zero total mass and trivial moment in the value group, then all edge slopes vanish and each chart part descends to a principal divisor on the corresponding component of the reduction. It is cited in the construction of nonzero functions with prescribed reduced divisors on a semistable covering and in the vanishing statement for the reduction map used for the toric part of the Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem
    AlgebraicCurve.mapDomain_placeMap_mem_principal_of_degree_eq_zero_of_forall_annulus_sum_eq_zero_of_prod_valuation_evalAt_zpow_eq_one
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (F : Type*) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField A) (Fbar i)]
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
    (f : F) (hf : f ≠ 0)
    (Di : Fin n → Divisor L F) (hdom : ∀ i, ∀ P ∈ (Di i).support, P ∈ (C i).dom)
    (hDi : ∀ i, ∀ P ∈ (C i).dom, Di i P = P.ord f)
    (hdeg : ∀ i, Divisor.degree (Di i) = 0)
    (N : Fin m → Divisor L F) (hNdom : ∀ e, ∀ P ∈ (N e).support, P ∈ (An e).dom)
    (hN : ∀ e, ∀ P ∈ (An e).dom, N e P = P.ord f)
    (hNsum : ∀ e, ((N e).sum fun _ k => k) = 0)
    (hNprod : ∀ e, ((N e).prod fun P k => A.valuation (P.evalAt (An e).param) ^ k) = 1) :
    ∀ i, Finsupp.mapDomain (C i).placeMap (Di i) ∈
      Divisor.principal (K := IsLocalRing.ResidueField A) (F := Fbar i) := by sorry
