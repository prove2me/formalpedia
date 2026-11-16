-- Prove2me | Theorems.Thm_FiniteGroupTesting_LinearQuery_Supplement_lemma_4_6
-- name    : FiniteGroupTesting.LinearQuery.Supplement.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:21:29.956135+00:00
-- url     : https://prove2.me/theorems/ad54247e-a202-4ed9-bdd8-24955779a23d
-- title:
--   Lemma 4.6 — Group-law transport with eta plus three delta
-- statement:
--   Let $G$ be a nonempty finite set with an arbitrary operation $*$, let $H$ be a group with $|H|=|G|$, and let $\Psi:G\rightharpoonup H$ have defect at most a real number $\delta$. Then there is a genuine group operation $\circ$ on all of $G$ such that
--   $$\operatorname{dist}(*,\circ)\le\eta(\Psi)+3\delta.$$
--   Here $\eta$ counts undefined locator values as multiplication failures and distance counts independent uniform ordered pairs. No uniformity or group promise is imposed on $x*y$. The result connects the two partial-map tests to the source's same-carrier distance.
--
--   Differences from the source:
--   - encoding: the input carrier G = [n] with operation *, and |G| = |H| = n → any nonempty finite type G with an arbitrary operation and |G| = |H|; reason: every nonempty finite type is a relabelling of [n]; distance and eta are invariant under relabelling
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), p. 29, Lemma 4.6

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

theorem lemma_4_6 {G H : Type} [Fintype G] [Fintype H] [Nonempty G]
    [Group H] (hcard : Fintype.card G = Fintype.card H) (op : G → G → G)
    (ψ : PartialMap G H) (δ : ℝ) (hδ : defect ψ ≤ δ) :
    ∃ law : G → G → G, IsGroupLaw law ∧ operationDistance op law ≤ eta op ψ + 3 * δ := by sorry

end FiniteGroupTesting.LinearQuery.Supplement
