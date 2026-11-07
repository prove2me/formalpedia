-- Prove2me | Theorems.Thm_BlockSSM_free_orbit_vector
-- name    : BlockSSM.free_orbit_vector
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:21:01.810796+00:00
-- url     : https://prove2.me/theorems/1a1909b4-36c9-425c-94bb-867ee81855a7
-- title:
--   A faithful representation of a finite group has a free-orbit vector
-- statement:
--   Let $\rho$ be a faithful complex representation of a finite group $H$ on a vector space $V$. Then there is a vector $v\in V$ such that
--   $$
--   h\longmapsto\rho(h)v
--   $$
--   is injective on $H$.
--
--   This vector is the start state of the tracker built from a cover: it lets a single hidden state remember which element of $H$ has been reached.
--
--   **Formalization Note** The case $V=0$ is allowed; faithfulness then forces $H$ to be trivial.
--
--   Differences from the source:
--   - generalization: $V$ finite-dimensional, as all representations in the paper → $V$ any complex vector space; reason: no dimension hypothesis is needed; finite-dimensional $V$ is a case
-- source:
--   C. Geng, The State Complexity of Block-Diagonal State Space Models, STOC 2027 submission manuscript (sha256 f9071794…), §3.1, p.3 (PDF p.4)

import Mathlib

namespace BlockSSM

/-- **A free-orbit vector.** Geng, *The State Complexity of Block-Diagonal State Space Models*, STOC 2027 submission manuscript (sha256 f9071794…), §3.1, p.3 (PDF p.4): "Because ρ is faithful, each nonidentity
h ∈ H fixes a proper subspace of V. A finite union of proper subspaces cannot cover a complex vector
space. Choose v outside that union. Then h ↦ ρ(h)v is injective."

**Formalization Note.** No dimension hypothesis on `V` is needed. `V = 0` is allowed: faithfulness
then forces `H` trivial. -/
theorem free_orbit_vector {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : Function.Injective ρ) :
    ∃ v : V, Function.Injective fun h : H => ρ h v := by sorry

end BlockSSM
