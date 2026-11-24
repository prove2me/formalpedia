-- Prove2me | Theorems.Thm_EquivariantHomogeneous_lifting_isomorphism_intertwines
-- name    : EquivariantHomogeneous.lifting_isomorphism_intertwines
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:32:26.337576+00:00
-- url     : https://prove2.me/theorems/0ecf0a03-5aae-4785-97e7-c606c80b2527
-- title:
--   Sections 2.3.2-2.4, Eqs. (2)-(4): the lifting isomorphism intertwines the induced representations
-- statement:
--   Let $G$ be a group, $H\le G$, $s$ a section of $G\to G/H$ with $s(H)=e$, and $\rho$ a representation of $H$ on a finite-dimensional real vector space $V$. Let $\Lambda$ and $\Lambda^{-1}$ be as in eq. (2), and let $\pi_G$ and $\pi_C$ be as in eqs. (3)-(4). Then:
--
--   1. $\Lambda f$ is a Mackey function for every $f:G/H\to V$;
--   2. $\Lambda^{-1}\Lambda f=f$ for every $f:G/H\to V$, and $\Lambda\Lambda^{-1}f'=f'$ for every Mackey function $f'$;
--   3. $\pi_G(g)$ maps Mackey functions to Mackey functions;
--   4. $\pi_C$ is a representation: $\pi_C(g_1g_2)=\pi_C(g_1)\pi_C(g_2)$ and $\pi_C(e)=\mathrm{id}$;
--   5. $\Lambda$ intertwines the two:
--   $$\pi_G(g)\circ\Lambda=\Lambda\circ\pi_C(g)\qquad\text{for all }g\in G.$$
--
--   So $\mathcal I_C$ and $\mathcal I_G$ carry isomorphic realisations of the induced representation $\mathrm{Ind}_H^G\rho$.
--
--   **Formalization Note** The paper's eq. (4) prints $\rho(\mathrm h(g^{-1},x)^{-1})$. The definition reads it as $\rho(\mathrm h(x,g^{-1})^{-1})$, the only reading compatible with the type $\mathrm h:G/H\times G\to H$; with it, items 4 and 5 hold. The section is global, since the statement holds for arbitrary groups and does not need local trivialisations.
-- source:
--   Cohen, Geiger and Weiler, A General Theory of Equivariant CNNs on Homogeneous Spaces, arXiv:1811.02017v2 (NeurIPS 2019), Section 2.3.2, Eq. (2), p. 5 and Section 2.4, Eqs. (3)-(4), p. 5

import Mathlib
import Definitions.Def_EquivariantHomogeneous_Basic

open EquivariantHomogeneous

namespace EquivariantHomogeneous

theorem lifting_isomorphism_intertwines {G : Type*} [Group G] {H : Subgroup G}
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (s : CosetSection H) (ρ : Representation ℝ H V) :
    (∀ f : G ⧸ H → V, liftSection s ρ f ∈ mackey ρ) ∧
    (∀ f : G ⧸ H → V, unliftSection s (liftSection s ρ f) = f) ∧
    (∀ f' ∈ mackey ρ, liftSection s ρ (unliftSection s f') = f') ∧
    (∀ (g : G) (f' : G → V), f' ∈ mackey ρ → indG g f' ∈ mackey ρ) ∧
    (∀ (g₁ g₂ : G) (f : G ⧸ H → V), indC s ρ (g₁ * g₂) f = indC s ρ g₁ (indC s ρ g₂ f)) ∧
    (∀ f : G ⧸ H → V, indC s ρ 1 f = f) ∧
    (∀ (g : G) (f : G ⧸ H → V), indG g (liftSection s ρ f) = liftSection s ρ (indC s ρ g f)) := by sorry

end EquivariantHomogeneous
