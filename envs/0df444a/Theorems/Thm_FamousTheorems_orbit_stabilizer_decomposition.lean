-- Prove2me | Theorems.Thm_FamousTheorems_orbit_stabilizer_decomposition
-- name    : FamousTheorems.orbit_stabilizer_decomposition
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T21:25:20.830992+00:00
-- url     : https://prove2.me/theorems/ab384477-9bd7-459e-a853-3015a0cd14c5
-- title:
--   The class equation (orbit decomposition of a group action)
-- statement:
--   **The class equation (orbit decomposition).** Let a group $G$ act on a set $X$. Then $X$ is in bijection with the disjoint union, over the orbits $\omega$ of the action, of the coset spaces $G/\operatorname{Stab}_G(x_\omega)$, where $x_\omega$ is a chosen representative of $\omega$:
--   $$X\;\cong\;\coprod_{\omega\in X/G} G/\operatorname{Stab}_G(x_\omega).$$
--
--   Counting both sides for finite $X$ gives $|X|=\sum_\omega [G:\operatorname{Stab}_G(x_\omega)]$. Applied to $G$ acting on itself by conjugation, this is the class equation $|G|=|Z(G)|+\sum[G:C_G(x)]$, the source of results such as the nontriviality of the centre of a $p$-group.
--
--   **Formalization note.** Mathlib's `MulAction.selfEquivSigmaOrbitsQuotientStabilizer`. The orbit space is `Quotient (MulAction.orbitRel G X)` and `ω.out` is a (choice-based) representative of the orbit `ω`. The statement asserts the existence of the bijection (`Nonempty` of the equivalence).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MulAction.selfEquivSigmaOrbitsQuotientStabilizer`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem orbit_stabilizer_decomposition (G X : Type*) [Group G] [MulAction G X] :
    Nonempty (X ≃ Σ ω : Quotient (MulAction.orbitRel G X), G ⧸ MulAction.stabilizer G ω.out) := by sorry

end FamousTheorems
