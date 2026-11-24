-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_4_5
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T20:20:49.497562+00:00
-- url     : https://prove2.me/theorems/cfc95f58-fd91-47af-ac0f-5e290264824a
-- title:
--   Lemma 4.5 — Attained defect identity
-- statement:
--   Let $G,H$ be nonempty finite sets of the same size $n$, and let $\Psi:G\rightharpoonup H$ be any partial map. Then
--   $$\operatorname{defect}(\Psi)=\min_{\pi:G\overset{\sim}{\longrightarrow}H}\Pr_{x\in G}[\Psi(x)\text{ undefined or }\Psi(x)\ne\pi(x)].$$
--   The minimum is attained by an actual bijection. This identifies image defect with the least disagreement probability and supplies the bijection needed for transport.
--
--   Differences from the source:
--   - encoding: minimum over bijections → IsLeast of the range of bijection error, including membership in that range; reason: this states both attainment and the bound for every bijection, without default infima
--   - encoding: |G| = |H| = n (Section 4.5) → nonempty finite types with equal cardinality; reason: n >= 1 throughout the paper, and defect divides by n
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 28, Lemma 4.5

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_4_5 {G H : Type} [Fintype G] [Fintype H] [Nonempty G]
    [Nonempty H] (hcard : Fintype.card G = Fintype.card H) (ψ : PartialMap G H) :
    IsLeast (Set.range (bijectionError ψ)) (defect ψ) := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
