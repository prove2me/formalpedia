-- Prove2me | Theorems.Thm_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq
-- name    : CerednikDrinfeld.ringHom_comp_eq_of_fstHom_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/e290a696-1c2a-5147-a34b-1c44dd87b1bc
-- title:
--   Ring maps W(k)→κ[ε] are fixed by κ-algebra endomorphisms
-- statement:
--   Let $p$ be a prime, let $k$ be a field of characteristic $p$ which is perfect in the sense that the Frobenius $x \mapsto x^p$ on $k$ is bijective, and let $\kappa$ be a field of characteristic $p$. Let $\psi \colon W(k) \to \kappa[\varepsilon]$ be a ring homomorphism from the ring of $p$-typical Witt vectors of $k$ to the dual numbers $\kappa[\varepsilon] = \kappa \oplus \kappa\varepsilon$ ($\varepsilon^2 = 0$), realised as the trivial square-zero extension of $\kappa$ by $\kappa$. Let $s \colon \kappa[\varepsilon] \to \kappa[\varepsilon]$ be a $\kappa$-algebra endomorphism which is compatible with the projection to the first coordinate, in the sense that the composite of $s$ with the $\kappa$-algebra homomorphism `TrivSqZeroExt.fstHom κ κ κ` (the map $a + b\varepsilon \mapsto a$) equals `TrivSqZeroExt.fstHom κ κ κ` itself. Then the composite of $\psi$ with the underlying ring homomorphism of $s$ equals $\psi$: that is, $s \circ \psi = \psi$ as ring homomorphisms $W(k) \to \kappa[\varepsilon]$.
--
--   A rigidity statement for tangent-level data in the Čerednik–Drinfeld part of the development: any ring homomorphism from the Witt vectors of a perfect field of characteristic $p$ into the dual numbers over a field of characteristic $p$ has no $\varepsilon$-component, hence is insensitive to deformations of the tangent direction. It is used in establishing an isomorphism of Cartier quadruples under transport of a line away from a node.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_ringHom_comp_eq_of_fstHom_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.ringHom_comp_eq_of_fstHom_comp_eq
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p]
    (κ : Type) [Field κ] [CharP κ p]
    (ψ : WittVector p k →+* DualNumber κ)
    (s : DualNumber κ →ₐ[κ] DualNumber κ)
    (hs : (TrivSqZeroExt.fstHom κ κ κ).comp s = TrivSqZeroExt.fstHom κ κ κ) :
    (s : DualNumber κ →+* DualNumber κ).comp ψ = ψ := by sorry
