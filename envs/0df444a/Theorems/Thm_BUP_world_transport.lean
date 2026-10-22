-- Prove2me | Theorems.Thm_BUP_world_transport
-- name    : BUP.world_transport
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T00:26:43.409457+00:00
-- url     : https://prove2.me/theorems/5fa094bc-9c63-4c61-9927-ab472a3483c3
-- title:
--   Transport of the diagram condition along equivalence of free involutions (Propositions 9 and 10)
-- statement:
--   If two involution extensions and two braid data are intertwined by isomorphisms - of the surface groups, the orbit groups, the pure braid groups, and the full braid groups - compatible with the covering injections, the deck projections, the braid inclusions, the braid projections, and the Fadell-Neuwirth projections, and the homomorphisms h and h' correspond under the isomorphism of the surface groups, then h admits the diagram of Proposition 6 in the first world if and only if h' does in the second. By Proposition 10 the equivalence classes of free involutions of a surface correspond to the equivalence classes of the induced short exact sequences, so this is the algebraic counterpart of the invariance of the Borsuk-Ulam property under equivalence of the free involutions.
-- source:
--   D. L. Goncalves, J. Guaschi, V. C. Laass, The Borsuk-Ulam property for homotopy classes of selfmaps of surfaces of Euler characteristic zero, arXiv:1608.00397 (2016), Section 2 (Propositions 9 and 10).

import Mathlib
import Definitions.Def_BUP_alg
import Definitions.Def_BUP_tor

namespace BUP

/-!  Milestone 2 (Propositions 9 and 10): the Borsuk-Ulam diagram condition is
invariant under transport along isomorphisms of the involution extension and
the braid data. If two involution extensions and two braid data are intertwined
by isomorphisms - of the surface groups, the orbit groups, the pure braid
groups, and the full braid groups - compatible with the injections, the deck
projections, the braid inclusions, the braid projections, and the
Fadell-Neuwirth projections, and the homomorphisms h and h' correspond under
the isomorphism of the surface groups, then h admits the diagram of
Proposition 6 if and only if h' does. This is the algebraic counterpart of the
invariance of the Borsuk-Ulam property under equivalence of the free
involutions. -/
theorem world_transport {A B P Bg A' B' P' Bg' : Type*} [Group A] [Group B] [Group P] [Group Bg]
    [Group A'] [Group B'] [Group P'] [Group Bg']
    (C : InvSES A B) (D : BraidData A P Bg) (C' : InvSES A' B') (D' : BraidData A' P' Bg')
    (eA : A ≃* A') (eB : B ≃* B') (eP : P ≃* P') (eBg : Bg ≃* Bg')
    (hc1 : ∀ a : A, eB (C.inj a) = C'.inj (eA a))
    (hc2 : ∀ b : B, C'.proj (eB b) = C.proj b)
    (hb1 : ∀ p : P, eBg (D.iota p) = D'.iota (eP p))
    (hb2 : ∀ g : Bg, D'.piBr (eBg g) = D.piBr g)
    (hb3 : ∀ p : P, eA (D.p1 p) = D'.p1 (eP p))
    (h : A →* A) (h' : A' →* A')
    (hcomm : ∀ a : A, eA (h a) = h' (eA a)) :
    NoBUP C D h ↔ NoBUP C' D' h' := by sorry

end BUP
