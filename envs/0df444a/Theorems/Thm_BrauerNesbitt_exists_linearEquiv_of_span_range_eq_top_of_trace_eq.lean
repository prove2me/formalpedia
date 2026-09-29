-- Prove2me | Theorems.Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq
-- name    : BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/cbb06456-5ba0-51cf-8390-395fdcafec9d
-- title:
--   Brauer–Nesbitt: equal traces and spanning image give isomorphism
-- statement:
--   Let $k$ be a field, $G$ a monoid, and let $V_1$, $V_2$ be finite-dimensional $k$-vector spaces with $V_1 \neq 0$. Let $\rho_1 : G \to \mathrm{End}_k(V_1)$ and $\rho_2 : G \to \mathrm{End}_k(V_2)$ be representations, i.e. monoid homomorphisms into the multiplicative monoids of $k$-linear endomorphisms. Assume that the image of each representation spans the full endomorphism algebra as a $k$-submodule: the $k$-span of $\{\rho_1(g) : g \in G\}$ is all of $\mathrm{End}_k(V_1)$, and likewise the $k$-span of $\{\rho_2(g) : g \in G\}$ is all of $\mathrm{End}_k(V_2)$. Assume further that the two representations have the same trace function, $\operatorname{tr}_{V_1}(\rho_1(g)) = \operatorname{tr}_{V_2}(\rho_2(g))$ for every $g \in G$. The conclusion is that there exists a $k$-linear isomorphism $e : V_1 \simeq V_2$ which intertwines the actions: $e(\rho_1(g)v) = \rho_2(g)(e(v))$ for all $g \in G$ and all $v \in V_1$. Nontriviality is assumed only of $V_1$; the spanning hypotheses replace any irreducibility or semisimplicity assumption.
--
--   This is the Brauer–Nesbitt criterion in the form used to recognise representations from their trace functions, with the classical hypothesis of absolute irreducibility replaced by the requirement that the operators $\rho_i(g)$ span the whole endomorphism algebra. It is invoked in the project where Galois representations with matching traces at Frobenius elements must be identified, for instance in the comparison of the residual representation of the Frey curve with the residual representation of a Hecke eigenform, and in the analysis of Hecke modules attached to modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BrauerNesbitt_exists_linearEquiv_of_span_range_eq_top_of_trace_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem BrauerNesbitt.exists_linearEquiv_of_span_range_eq_top_of_trace_eq {k : Type*} {G : Type*}
  {V₁ : Type*} {V₂ : Type*} [Field k] [Monoid G] [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
  [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂] (ρ₁ : Representation k G V₁)
  (ρ₂ : Representation k G V₂) [Nontrivial V₁] (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
  (hspan₂ : Submodule.span k (Set.range ⇑ρ₂) = ⊤)
  (htr : ∀ (g : G), (LinearMap.trace k V₁) (ρ₁ g) = (LinearMap.trace k V₂) (ρ₂ g)) :
  ∃ e : V₁ ≃ₗ[k] V₂, ∀ (g : G) (v : V₁), e ((ρ₁ g) v) = (ρ₂ g) (e v) := by sorry
