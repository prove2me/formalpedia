-- Prove2me | Theorems.Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero
-- name    : CerednikDrinfeld.EdgeFamily.edgeRingCharP.exists_ker_le_and_forall_ker_le_of_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/398729a3-80a9-5420-aa36-081943028cc6
-- title:
--   Branch-generic point of the edge chart dominating node points
-- statement:
--   Fix a natural number $p$ carrying the hypothesis that it is prime, a field $k$, and write $E =$ `EdgeFamily.edgeRingCharP p k` for the edge chart ring attached to $p$ and $k$, namely the localisation of the edge quotient ring away from the element `edgeQuot.discr k (0 : k) p` (the chart ring `FormalOmega.chartERing` formed with uniformiser $0 \in k$ and parameter $p$); it carries two distinguished elements `EdgeFamily.edgeRingCharP.ξ p k` and `EdgeFamily.edgeRingCharP.η p k`. Let $\kappa$ be a field and $f \colon E \to \kappa$ an arbitrary ring homomorphism. The assertion is that there exist a type $L$, a field structure on $L$, and a ring homomorphism $h \colon E \to L$ such that, first, $\ker h \subseteq \ker f$, and, second, for every field $\kappa_0$ and every ring homomorphism $f_0 \colon E \to \kappa_0$ with $f_0(\xi) = 0$ and $f_0(\eta) = 0$ one again has $\ker h \subseteq \ker f_0$. Thus a single point of the edge chart specialises both to the given point $f$ and to every point supported at the node $\xi = \eta = 0$.
--
--   This is the branch-genericity statement for the reduced edge chart of the Čerednik–Drinfeld model: any field-valued point of the chart, together with all points lying at the node, is dominated by one point of the chart, so identities valid at that point propagate to both. It is used in the construction of Cartier quadruples along edge isogenies and in the recognition of height-four isogenies over the edge chart ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_exists_ker_le_and_forall_ker_le_of_apply_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld

theorem CerednikDrinfeld.EdgeFamily.edgeRingCharP.exists_ker_le_and_forall_ker_le_of_apply_eq_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    (κ : Type) [Field κ] (f : EdgeFamily.edgeRingCharP p k →+* κ) :
    ∃ (L : Type) (_ : Field L) (h : EdgeFamily.edgeRingCharP p k →+* L),
      RingHom.ker h ≤ RingHom.ker f ∧
      ∀ (κ₀ : Type) [Field κ₀] (f₀ : EdgeFamily.edgeRingCharP p k →+* κ₀),
        f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0 → f₀ (EdgeFamily.edgeRingCharP.η p k) = 0 →
        RingHom.ker h ≤ RingHom.ker f₀ := by sorry
