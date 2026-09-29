-- Prove2me | Theorems.Thm_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
-- name    : AlgebraicCurve.ComponentChart.eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.008273+00:00
-- url     : https://prove2.me/theorems/428e1823-508c-5e44-8b7e-5486d52bc5f8
-- title:
--   Centre dichotomy for valuation rings over a component chart
-- statement:
--   Let $L$ be a field, $A \subseteq L$ a valuation subring, $F/L$ a field extension, and $\bar F$ a field extension of the residue field of $A$; let $C$ be a component chart of $F$ over $A$ with values in $\bar F$, so that $C$ carries a valuation subring `C.integers` of $F$ with a surjective residue homomorphism onto $\bar F$ whose kernel is the maximal ideal, a set `C.dom` of places of $F/L$ and the further compatibility data of a `ComponentChart`. Call $f \in F$ tube-bounded when for every $P \in C.\mathrm{dom}$ one has $f \in \mathcal O_P$ and $P$-evaluation $P.\mathrm{evalAt}\, f$ lies in $A$. Let $N$ be a finite, nonempty set of places of $\bar F$ over the residue field of $A$, and assume: (i) $C$ has affinoid lifting relative to $N$, i.e. every tube-bounded $f$ lies in `C.integers`, every $g \in \bar F$ lying in $\mathcal O_Q$ for all $Q \notin N$ is the residue of some tube-bounded element of `C.integers`, and every $h \in$ `C.integers` satisfies $hs = r$ for some tube-bounded $r$ and some tube-bounded $s \in$ `C.integers` with nonzero residue; (ii) the place dictionary holds for $N$: the maximal ideals of $\mathrm{regOff}\,N = \bigcap_{Q \notin N} \mathcal O_Q \subseteq \bar F$ correspond bijectively to the places $Q \notin N$, a maximal ideal matching $Q$ exactly when its elements are those $g$ with $g = 0$ or $\mathrm{ord}_Q g > 0$; (iii) the residue of every tube-bounded element of `C.integers` lies in $\mathcal O_Q$ for all $Q \notin N$; (iv) every nonzero prime ideal of $\mathrm{regOff}\,N$ is maximal; (v) every $P \in C.\mathrm{dom}$ is rational, i.e. $L$ surjects onto the residue field of $P$. Let finally $O$ be a valuation subring of $F$ with $O \cap L = A$ (precisely: $\mathrm{alg}_{L \to F}(x) \in O \iff x \in A$) which contains every tube-bounded element of $F$. Then either $O =$ `C.integers`, or there is exactly one place $Q$ of $\bar F$ over the residue field of $A$ which is a centre of $O$ in the sense that $Q \notin N$ and, for every tube-bounded $f \in$ `C.integers`, the residue of $f$ either vanishes or has $\mathrm{ord}_Q > 0$ precisely when $f$ belongs to the maximal ideal of $O$.
--
--   This is the dichotomy, familiar from the rigid-analytic theory of reductions of affinoids, between the Gauss valuation attached to a component and the valuations specialising to a single point of the affine reduction obtained by deleting the places of $N$: a valuation ring prolonging $A$ and bounded on the tube is either the chart's own ring of integers or has a unique centre among the places off $N$. It is used in the identification of the ring of integers of the component charts of modular curves at full level, in the three `ModularCurve.FullLevel` results on charts over a curve, including the cases of residue characteristic dividing $3$ and $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ComponentChart_eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableChartsComap
import Definitions.Def_AlgebraicCurve_AffinoidCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicCurve

open IsLocalRing
open scoped Pointwise

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ComponentChart.eq_integers_or_existsUnique_isCentre_of_forall_tubeBounded_mem_of_regular
    (C : ComponentChart A F Fbar) (N : Finset (Place (ResidueField A) Fbar))
    (hC : C.HasAffinoidLifting N) (hdict : ComponentChart.HasPlaceDictionary (A := A) N)
    (hreg : ∀ (f : F) (hf : f ∈ C.integers), C.tubeBounded f →
      ∀ Q : Place (ResidueField A) Fbar, Q ∉ N → C.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)
    (hdim : ∀ 𝔭 : Ideal (ComponentChart.regOff (A := A) N), 𝔭.IsPrime → 𝔭 ≠ ⊥ → 𝔭.IsMaximal)
    (hN : N.Nonempty) (hrat : ∀ P ∈ C.dom, P.IsRational)
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    (hRO : ∀ f : F, C.tubeBounded f → f ∈ O) :
    O = C.integers ∨ ∃! Q : Place (ResidueField A) Fbar, C.IsCentre N O Q := by sorry
