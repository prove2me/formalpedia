-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor
-- name    : AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/918a8879-19ea-59b0-b262-f6d6dd87a646
-- title:
--   Chordal proximity on a component chart equals the disc kernel
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ satisfying `HasPrincipalDivisors L F`, so that each nonzero $f \in F$ admits a divisor of degree $0$ whose coefficient at every place $v$ of $F/L$ is $v.\mathrm{ord}(f)$; let $\bar F$ be a field extension of the residue field of $A$, and let $C$ be a `ComponentChart A F Fbar`, i.e. a valuation subring $C.\mathrm{integers} \subseteq F$ with a surjective reduction homomorphism $C.\mathrm{residue}$ onto $\bar F$ whose kernel is the maximal ideal, a set $C.\mathrm{dom}$ of places of $F/L$, a finite set $C.\mathrm{nodes}$ of places of $\bar F$ over the residue field of $A$, and a specialisation map $C.\mathrm{placeMap}$ on places, subject to the chart axioms. Given $r \in \mathbb{N}$, a family $s : \mathrm{Fin}\,r \to F$ with all $s_i \in C.\mathrm{integers}$, and two index assignments $cQ, iQ$ on places of $\bar F$ (a pivot and an immersion index for each reduced point), assume: every $P \in C.\mathrm{dom}$ and its image $C.\mathrm{placeMap}\,P$ are rational, in the sense that the structure map into the residue field is surjective; the chart reduction of the pivot $s_{cQ(C.\mathrm{placeMap}\,P)}$ is nonzero; all ratios $s_j \cdot s_{cQ(C.\mathrm{placeMap}\,P)}^{-1}$ lie both in $C.\mathrm{integers}$ and in the valuation subring of $P$; the reduction of the immersion ratio $s_{iQ(C.\mathrm{placeMap}\,P)} \cdot s_{cQ(C.\mathrm{placeMap}\,P)}^{-1}$ minus the image of its value at $C.\mathrm{placeMap}\,P$ has order exactly $1$ there; and for $P, Q \in C.\mathrm{dom}$ with $C.\mathrm{placeMap}\,P \neq C.\mathrm{placeMap}\,Q$, the two vectors of values at $C.\mathrm{placeMap}\,P$ and $C.\mathrm{placeMap}\,Q$ of the reductions of the ratios normalised at each place's own pivot have some nonvanishing $2 \times 2$ minor. The conclusion: for every nonarchimedean absolute value $\mu$ on $L$ with $A = \{a : \mu(a) \le 1\}$ and all distinct $P, Q \in C.\mathrm{dom}$, the chordal proximity $\mathrm{prox}$ of the two value vectors $i \mapsto P.\mathrm{evalAt}(s_i \cdot s_{cQ(C.\mathrm{placeMap}\,P)}^{-1})$ and $i \mapsto Q.\mathrm{evalAt}(s_i \cdot s_{cQ(C.\mathrm{placeMap}\,Q)}^{-1})$ — that is, $\log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$, where $\mathrm{evalAt}$ denotes the chosen preimage in $L$ of the residue class — vanishes when $C.\mathrm{placeMap}\,P \neq C.\mathrm{placeMap}\,Q$, and equals $-\log \mu\bigl(Q.\mathrm{evalAt}(t) - P.\mathrm{evalAt}(t)\bigr)$, with $t$ the immersion ratio at $C.\mathrm{placeMap}\,P$, when $C.\mathrm{placeMap}\,P = C.\mathrm{placeMap}\,Q$ (both vectors then being normalised at the common pivot).
--
--   This is the per-chart comparison in the construction of the semistable Green kernel: on a component chart it identifies the chordal proximity of two distinct places with the disc kernel $-\log\mu$ of the difference of their immersion coordinates when they specialise to the same point of the component, and shows it vanishes when they specialise to different points. It is used in the chart-comparison statement [`AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec`](thm.html#AlgebraicCurve.ComponentChart.chartComparison_of_chartData_of_mulVec) and, through it, in [`ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd); the proof cites only the two elementary nonarchimedean identities [`AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart`](thm.html#AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart) and [`AlgebraicCurve.prox_eq_zero_of_far_of_chart`](thm.html#AlgebraicCurve.prox_eq_zero_of_far_of_chart).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_prox_eq_of_chartData_of_minor.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing

theorem AlgebraicCurve.ComponentChart.prox_eq_of_chartData_of_minor
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    [HasPrincipalDivisors L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (C : ComponentChart A F Fbar) {r : ℕ} (s : Fin r → F) (hint : ∀ i, s i ∈ C.integers)
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P ∈ C.dom, P.IsRational ∧ (C.placeMap P).IsRational)
    (hcQ : ∀ P ∈ C.dom, C.residue ⟨s (cQ (C.placeMap P)), hint _⟩ ≠ 0)
    (hratio : ∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
    (hreg : ∀ P ∈ C.dom, ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ P.toValuationSubring)
    (himm : ∀ P ∈ C.dom, ∀ hmem : s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers,
      (C.placeMap P).ord (C.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((C.placeMap P).evalAt (C.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P ∈ C.dom, ∀ Q ∈ C.dom, C.placeMap P ≠ C.placeMap Q →
      ∀ (hmP : ∀ j, s j * (s (cQ (C.placeMap P)))⁻¹ ∈ C.integers)
        (hmQ : ∀ j, s j * (s (cQ (C.placeMap Q)))⁻¹ ∈ C.integers),
      ∃ i j, (C.placeMap P).evalAt (C.residue ⟨_, hmP i⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ j⟩)
        ≠ (C.placeMap P).evalAt (C.residue ⟨_, hmP j⟩) * (C.placeMap Q).evalAt (C.residue ⟨_, hmQ i⟩)) :
    ∀ μ : AbsoluteValue L ℝ, IsNonarchimedean μ → (∀ a : L, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ C.dom, ∀ Q ∈ C.dom, P ≠ Q →
        (C.placeMap P ≠ C.placeMap Q →
          prox (μ : L → ℝ) (fun i ↦ P.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            (fun i ↦ Q.evalAt (s i * (s (cQ (C.placeMap Q)))⁻¹)) = 0) ∧
        (C.placeMap P = C.placeMap Q →
          prox (μ : L → ℝ) (fun i ↦ P.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            (fun i ↦ Q.evalAt (s i * (s (cQ (C.placeMap P)))⁻¹))
            = -Real.log (μ (Q.evalAt (s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹)
                - P.evalAt (s (iQ (C.placeMap P)) * (s (cQ (C.placeMap P)))⁻¹)))) := by sorry
