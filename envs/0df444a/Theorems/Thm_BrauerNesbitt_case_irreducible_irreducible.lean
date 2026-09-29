-- Prove2me | Theorems.Thm_BrauerNesbitt_case_irreducible_irreducible
-- name    : BrauerNesbitt.case_irreducible_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/84dcad7a-ae52-568b-a545-7d63638c4c76
-- title:
--   Brauer–Nesbitt: irreducibles with equal traces are isomorphic
-- statement:
--   Let $k$ be a field and $G$ a monoid, and let $V_1$, $V_2$ be $k$-vector spaces (given as additive commutative groups with $k$-module structures) that are finite-dimensional over $k$. Let $\rho_1 : G \to \operatorname{End}_k(V_1)$ and $\rho_2 : G \to \operatorname{End}_k(V_2)$ be representations of $G$ over $k$, that is, monoid homomorphisms into the endomorphism monoids. Assume $k$ is algebraically closed, and assume each of $\rho_1$ and $\rho_2$ satisfies the irreducibility predicate `Representation.IsIrreducible` for representations. The hypothesis `htr` is that the two characters agree pointwise on all of $G$: for every $g \in G$, $\operatorname{tr}_k(\rho_1(g)) = \operatorname{tr}_k(\rho_2(g))$, the traces being taken as $k$-linear endomorphisms of $V_1$ and $V_2$ respectively. The conclusion is the existence of a $k$-linear isomorphism $e : V_1 \xrightarrow{\sim} V_2$ which intertwines the two actions, i.e. $e(\rho_1(g)v) = \rho_2(g)(e(v))$ for every $g \in G$ and every $v \in V_1$. Only existence of such an intertwiner is asserted; no normalisation or uniqueness up to scalar is claimed.
--
--   This is the irreducible case of the Brauer–Nesbitt theorem: over an algebraically closed field, an irreducible finite-dimensional representation of a monoid is determined up to isomorphism by its trace function. It is used in the Langlands–Tunnell part of the development, where two Galois representations known to have equal traces (in practice at Frobenius elements, via Chebotarev) must be identified; it is cited by [`LanglandsTunnell.CubicInduction.exists_pairing_transposeInv3_of_isIrreducibleRep`](thm.html#LanglandsTunnell.CubicInduction.exists_pairing_transposeInv3_of_isIrreducibleRep).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BrauerNesbitt_case_irreducible_irreducible.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem BrauerNesbitt.case_irreducible_irreducible {k : Type*} {G : Type*} {V₁ : Type*}
  {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁] [AddCommGroup V₂]
  [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁) (ρ₂ : Representation k G V₂)
  [IsAlgClosed k] [ρ₁.IsIrreducible] [ρ₂.IsIrreducible]
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v) := by sorry
