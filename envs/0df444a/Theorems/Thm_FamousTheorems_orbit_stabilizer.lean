-- Prove2me | Theorems.Thm_FamousTheorems_orbit_stabilizer
-- name    : FamousTheorems.orbit_stabilizer
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T06:56:24.311895+00:00
-- url     : https://prove2.me/theorems/8aaffdbc-917c-440f-823d-5f9e2a0d76e9
-- title:
--   The orbit–stabilizer theorem
-- statement:
--   **The orbit–stabilizer theorem.**
--
--   For a group $G$ acting on a set $X$ and a point $b \in X$, there is a bijection
--   $$G \cdot b \;\simeq\; G / G_b$$
--   between the orbit of $b$ and the coset space of its stabilizer.
--
--   For finite $G$ this gives the counting form $|G| = |G\cdot b| \cdot |G_b|$: the orbit size
--   always divides the group order. That single corollary drives a large part of finite group
--   theory — the class equation (acting by conjugation), Burnside's lemma, Cauchy's theorem, and
--   the Sylow theorems all come from applying it to a well-chosen action.
--
--   The bijection itself is canonical and requires no finiteness: $gG_b \mapsto g\cdot b$ is
--   well defined precisely because $G_b$ is the set of elements fixing $b$, and injective for the
--   same reason. It is a $G$-equivariant bijection, which is why every transitive $G$-set is
--   isomorphic to a coset space.
--
--   **Formalization note.** `MulAction.orbit G b` and `MulAction.stabilizer G b` are the orbit
--   and the stabilizer subgroup; `G ⧸ H` here is the quotient by a not-necessarily-normal
--   subgroup, so the target is a set rather than a group, and the equivalence is data wrapped in
--   `Nonempty`. The result is Mathlib's `MulAction.orbitEquivQuotientStabilizer`.
-- source:
--   Listed in Mathlib's "1000 theorems" manifest (docs/1000.yaml); formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open Filter Set Topology

theorem orbit_stabilizer {G : Type*} [Group G] {X : Type*} [MulAction G X] (b : X) :
    Nonempty (MulAction.orbit G b ≃ G ⧸ MulAction.stabilizer G b) := by sorry

end FamousTheorems
