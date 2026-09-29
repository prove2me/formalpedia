-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec
-- name    : AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/6e8be971-edd7-5b69-85d0-0db2adbdb969
-- title:
--   Chart comparison for proximity of evaluation vectors under a bounded linear change
-- statement:
--   Let $F$ be a field over $\overline{\mathbb Q}$ in which every nonzero element has a degree-zero principal divisor, let $A$ be a valuation subring of $\overline{\mathbb Q}$, let $p$ be a prime, let $\bar F$ be a field over the residue field of $A$, and let $C$ be a component chart for $A$, $F$, $\bar F$, i.e. a valuation subring $C.\mathrm{integers}\subseteq F$ with a surjective residue homomorphism $C.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/\overline{\mathbb Q}$, a finite set of nodes, and a reduction map $C.\mathrm{placeMap}$ on places satisfying the chart axioms. Let $s,t:\mathrm{Fin}\,r\to F$ with all $s_i\ne 0$, and let $cQ,iQ$ assign to each place of $\bar F$ over the residue field of $A$ an index. Assume the chart data for $t$: each $t_i\in C.\mathrm{integers}$; every $P\in C.\mathrm{dom}$ and its reduction $\bar P=C.\mathrm{placeMap}\,P$ are rational (the structure map into the residue field is surjective); $C.\mathrm{residue}$ of $t_{cQ(\bar P)}$ is nonzero; all ratios $t_j\,t_{cQ(\bar P)}^{-1}$ lie in $C.\mathrm{integers}$ and in the valuation subring of $P$; the reduction of $t_{iQ(\bar P)}\,t_{cQ(\bar P)}^{-1}$ minus the image of its value $\mathrm{evalAt}$ at $\bar P$ has $\mathrm{ord}$ equal to $1$ at $\bar P$ (here $\mathrm{ord}_v f=-\log$ of the adic valuation, and $\mathrm{evalAt}$ is the value in the base field of the residue of $f$, or $0$ off the valuation subring); and for $P,Q\in C.\mathrm{dom}$ with $\bar P\ne\bar Q$ some $2\times2$ minor of the two rows of values at $\bar P$ and $\bar Q$ of the reduced ratios is nonzero. Assume further matrices $M,M^{-1}$ over $\overline{\mathbb Q}$ with $M^{-1}M=1$ and $B\in\mathbb N$ with $p^B M_{ij},\,p^B (M^{-1})_{ij}\in A$ for all $i,j$, and the link: for each $P\in C.\mathrm{dom}$ there is $d\ne0$ with $\mathrm{evalVec}\,s\,P=d\cdot M\big(P.\mathrm{evalAt}(t_j t_{cQ(\bar P)}^{-1})\big)_j$, where $\mathrm{evalVec}\,s\,P$ is the vector of values at $P$ of the $s_i$ normalised by the pivot entry of minimal $\mathrm{ord}$. Finally let $T$ assign to each place of $\bar F$ an element of $F$ such that for $P\in C.\mathrm{dom}$ the difference $T(\bar P)-P.\mathrm{evalAt}(T(\bar P))$ lies in $C.\mathrm{integers}$, has nonzero residue of $\mathrm{ord}$ one at $\bar P$, has positive $\mathrm{ord}$ at $P$, and $\mathrm{ord}$ zero at every other $Q\in C.\mathrm{dom}$ with $\bar Q=\bar P$. Then for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, and all $P\ne Q$ in $C.\mathrm{dom}$ whose evaluation vectors admit a nonvanishing $2\times 2$ minor: if $\bar P=\bar Q$ then $\big|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,P,\mathrm{evalVec}\,s\,Q)+\log\mu\big(P.\mathrm{evalAt}(T(\bar P))-Q.\mathrm{evalAt}(T(\bar P))\big)\big|\le 4B\,(-\log\mu(p))$, and if $\bar P\ne\bar Q$ then $\big|\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,P,\mathrm{evalVec}\,s\,Q)\big|\le 4B\,(-\log\mu(p))$, where $\mathrm{prox}_\mu(x,y)=\log\sup_i\mu(x_i)+\log\sup_i\mu(y_i)-\log\sup_{i,j}\mu(x_iy_j-x_jy_i)$.
--
--   This is the per-chart comparison statement for chordal proximity: on a single component of a semistable reduction it identifies, up to an error $4B\,(-\log\mu(p))$ controlled by the denominators of the linear change of coordinates $M$, the proximity of two evaluation vectors of the family $s$ with $-\log\mu$ of the difference of the values of a disc parameter $T$ when the two places reduce to the same point, and with $0$ when they reduce to different points. It is used by the two multiplicative-covering chart comparisons [`ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord`](thm.html#ModularCurve.MultCovering.chartComparison_infChart_of_fibreCoord) and [`ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord`](thm.html#ModularCurve.MultCovering.chartComparison_zeroChart_of_chartData_of_fibreCoord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_chartComparison_of_chartData_of_mulVec.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec
    {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] [HasPrincipalDivisors (AlgebraicClosure ℚ) F]
    {A : ValuationSubring (AlgebraicClosure ℚ)} (p : ℕ) (hp : p.Prime)
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {r : ℕ} (s t : Fin r → F) (hs0 : ∀ i, s i ≠ 0)

    (hint : ∀ i, t i ∈ C.integers)
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational)
    (hcQ : ∀ P ∈ C.dom, C.residue ⟨t (cQ (C.placeMap P)), hint _⟩ ≠ 0)
    (hratio : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
    (hreg : ∀ P ∈ C.dom, ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ C.dom, ∀ hmem : t (iQ (C.placeMap P)) * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
      (C.placeMap P).ord (C.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
      ∀ (hmP : ∀ j, t j * (t (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
        (hmQ : ∀ j, t j * (t (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
      ∃ i j, (C.placeMap P).evalAt (C.residue ⟨_, hmP i⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j⟩)
        ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i⟩))

    (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (hM : Minv * M = 1) (B : ℕ)
    (hMB : ∀ i j, (p : AlgebraicClosure ℚ) ^ B * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ B * Minv i j ∈ A)
    (hlink : ∀ P ∈ C.dom, ∃ d : AlgebraicClosure ℚ, d ≠ 0 ∧
      evalVec s P = d • M.mulVec (fun i => P.evalAt (t i * (t (cQ (C.placeMap P)))⁻¹)))

    (T : Place (ResidueField A) Fbar → F)
    (hT : ∀ P ∈ C.dom,
      ∃ h : T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P))) ∈ C.integers,
        C.residue ⟨_, h⟩ ≠ 0 ∧ (C.placeMap P).ord (C.residue ⟨_, h⟩) = 1 ∧
        0 < P.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) ∧
        ∀ Q ∈ C.dom, C.placeMap Q = C.placeMap P → Q ≠ P →
          Q.ord (T (C.placeMap P) - algebraMap (AlgebraicClosure ℚ) F (P.evalAt (T (C.placeMap P)))) = 0) :
    ∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ C.dom, ∀ Q ∈ C.dom, P ≠ Q →
        (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
        ((C.placeMap P = C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (T (C.placeMap P)) - Q.evalAt (T (C.placeMap P))))|
            ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
        (C.placeMap P ≠ C.placeMap Q →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ (4 * B : ℝ) * (-Real.log (μ (p : AlgebraicClosure ℚ))))) := by sorry
