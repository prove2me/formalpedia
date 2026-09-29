-- Prove2me | Theorems.Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
-- name    : CerednikDrinfeld.EdgeFamily.edgeRingCharP.eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/4f7ce118-f32e-5f35-8dbc-736e1353f18a
-- title:
--   Maps out of the edge chart ring killing ξ,η factor through the node
-- statement:
--   Fix a prime $p$, a commutative ring $k$ and a commutative ring $\Omega$. Write $E =$ `EdgeFamily.edgeRingCharP p k`, which by definition is `FormalOmega.chartERing k (0 : k) p`, the localisation away from the element `edgeQuot.discr k 0 p` of the edge quotient ring built from $k$ with parameter $\pi = 0$ and $q = p$; it carries a $k$-algebra structure, and `EdgeFamily.edgeRingCharP.ξ p k` and `EdgeFamily.edgeRingCharP.η p k` are its two distinguished elements $\xi,\eta$. Assume given a ring homomorphism $f_0 \colon E \to k$ that splits the structure map, i.e. $f_0 \circ (\text{algebraMap } k\, E) = \mathrm{id}_k$, and satisfies $f_0(\xi) = 0$ and $f_0(\eta) = 0$; and a ring homomorphism $y \colon E \to \Omega$ with $y(\xi) = 0$ and $y(\eta) = 0$. The conclusion is the equality of ring homomorphisms $y = (y \circ (\text{algebraMap } k\, E)) \circ f_0$: that is, $y$ is the composite of $f_0$ with the restriction of $y$ to $k$.
--
--   This is the rigidity statement that a point of the edge chart ring at which both coordinates $\xi,\eta$ vanish — a point lying over the node of the edge — is the base change along $k \to \Omega$ of the node section $f_0$. It is used in [`CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero`](thm.html#CerednikDrinfeld.FormalODModule.exists_isCartierQuadruple_map_line_eq_of_edge_isogeny_of_apply_xi_eq_zero_of_apply_eta_eq_zero) to identify the fibre of a family over the edge chart at such a point with the corresponding base change of its fibre at the node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_EdgeFamily_edgeRingCharP_eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.FormalOmega

theorem CerednikDrinfeld.EdgeFamily.edgeRingCharP.eq_comp_of_apply_xi_eq_zero_of_apply_eta_eq_zero
    (p : ℕ) [Fact p.Prime] (k : Type) [CommRing k] {Ω : Type} [CommRing Ω]
    (f₀ : EdgeFamily.edgeRingCharP p k →+* k)
    (hf₀ : f₀.comp (algebraMap k (EdgeFamily.edgeRingCharP p k)) = RingHom.id k)
    (hf₀ξ : f₀ (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hf₀η : f₀ (EdgeFamily.edgeRingCharP.η p k) = 0)
    (y : EdgeFamily.edgeRingCharP p k →+* Ω)
    (hyξ : y (EdgeFamily.edgeRingCharP.ξ p k) = 0) (hyη : y (EdgeFamily.edgeRingCharP.η p k) = 0) :
    y = (y.comp (algebraMap k (EdgeFamily.edgeRingCharP p k))).comp f₀ := by sorry
