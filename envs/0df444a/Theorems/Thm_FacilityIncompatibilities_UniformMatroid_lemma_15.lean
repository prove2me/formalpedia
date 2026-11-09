-- Prove2me | Theorems.Thm_FacilityIncompatibilities_UniformMatroid_lemma_15
-- name    : FacilityIncompatibilities.UniformMatroid.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:20:21.961984+00:00
-- url     : https://prove2.me/theorems/1ef55e95-f446-4b3c-9c20-3a12608e4968
-- title:
--   Lemma 15 — uniform opening costs: F(P) ≤ F*
-- statement:
--   Let $(V_C,V_F,d,f,\mathcal M)$ be an FL-MI instance with uniform opening costs, $S$ a locally optimal feasible facility set, $O$ a facility set with a minimum-cost feasible assignment $\sigma_O$, $\mu$ the injection of §2.1 (when $|O|<|S|$: a minimum-cost injection $O\to S$ fixing $O\cap S$) and $\pi$ the assignment of §2.1 (a $W$-minimizer to $S$, tie-broken by $q$ when $|O|<|S|$). With $P=\pi(V_C)$ and $F^*=F(O)$,
--
--   $$F(P)\le F^*.$$
--
--   Together with Lemmas 5 and 10 it gives $C+F\le 3C^*+2F^*$, and after rescaling opening costs the $(1+\sqrt2)$ bound of Theorem 3.
--
--   Differences from the source:
--   - generalization: metric distances d on V_C ∪ V_F (Definition 1) → a pseudometric: d(x,x)=0, symmetry and the triangle inequality, distinct points may be at distance 0; reason: every metric satisfies these axioms, so every instance of the source is covered
--   - generalization: O a fixed globally optimal solution with optimal assignment σ_O (§2.1, printed p.5) → O any facility set with a minimum-cost feasible assignment σ_O (any feasible O); reason: §3 (printed p.13) states the analysis does not require optimality of O and uses it for a non-optimal O after rescaling; an optimum is a special case
-- source:
--   Pengfei Wu, Zachary Friggstad, Facility Location with Customer Incompatibilities, STOC 2027 submission #664 (October 2026), SHA-256 e95d28b65476bd15332cddbb49bb8bfb3c370bb260b03d92b35425595cdb7ab3, Lemma 15, printed p.13 / PDF p.14

import Mathlib
import Definitions.Def_FacilityIncompatibilities_UniformMatroid_Compression

namespace FacilityIncompatibilities.UniformMatroid

/-- **Lemma 15** (printed p.13 / PDF p.14): for FL-MI with uniform opening costs, a local minimum
`S` satisfies `F(P) ≤ F*`, where `P = π(V_C)` for the `π` of §2.1 and `F* = F(O)`. -/
theorem lemma_15 {C F : Type*} [Fintype C] [Fintype F] [DecidableEq F] (I : Instance C F)
    (hI : I.Valid) (hU : I.IsUniform) (S O : Finset F) (σO : C → F) (μ : F → F) (π : C → F)
    (hS : I.IsLocalOpt S) (hσO : I.IsOptAssignment O σO)
    (hμ : I.IsSection21Injection O S μ) (hπ : I.IsTieBrokenWMin S O σO μ π) :
    I.openCost (assignImage π) ≤ I.openCost O := by sorry

end FacilityIncompatibilities.UniformMatroid
