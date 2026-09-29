-- Prove2me | Theorems.Thm_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd
-- name    : BostonLenstraRibet.exists_embedding_of_irreducible_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/5383ebc6-488a-509a-a8f3-eee877b473bc
-- title:
--   Boston–Lenstra–Ribet embedding for odd irreducible ρ
-- statement:
--   Let $k$ be a field, $G$ a group and $V$ a $k$-vector space carrying a representation $\rho_V$ of $G$ (a homomorphism $G \to \mathrm{GL}_k(V)$, whose values are viewed as elements of $\mathrm{End}_k(V)$). Let $\rho : G \to M_2(k)$ be any map that is multiplicative, $\rho(\sigma\tau) = \rho(\sigma)\rho(\tau)$ for all $\sigma,\tau \in G$. Assume: (i) for every $\sigma \in G$ the endomorphism $\rho_V(\sigma)$ satisfies the characteristic polynomial of the matrix $\rho(\sigma)$, i.e. $\rho_V(\sigma)\circ\rho_V(\sigma) - \operatorname{tr}(\rho(\sigma))\,\rho_V(\sigma) + \det(\rho(\sigma))\,\mathrm{id}_V = 0$; (ii) $\rho$ is irreducible in the sense that every $k$-submodule $W \subseteq k^2$ with $(\rho g)\cdot v \in W$ for all $g \in G$ and $v \in W$ is either $\bot$ or $\top$; (iii) there is an element $c \in G$ with $\rho(c)^2 = 1$ and $\det(\rho(c)) = -1$; (iv) $2 \neq 0$ in $k$; and (v) $V \neq 0$, in the form that some $v \in V$ is nonzero. The conclusion is that there exists an injective $k$-linear map $\varphi : k^2 \to V$ which is equivariant, $\varphi((\rho\sigma)\cdot v) = \rho_V(\sigma)(\varphi v)$ for all $\sigma \in G$ and $v \in k^2$; that is, the standard two-dimensional module of $\rho$ embeds into $V$ compatibly with the $G$-actions.
--
--   This is the Boston–Lenstra–Ribet result on quotients of group rings, in embedding rather than full isotypicity form: it produces one copy of $\rho$ inside a nonzero module all of whose group elements satisfy the Cayley–Hamilton identities of $\rho$, rather than a decomposition $V \cong \rho^{\oplus r}$. It is the module-theoretic input to level lowering, where $V$ is a space of torsion points on a Jacobian, the quadratic identities come from the Eichler–Shimura relation at Frobenius elements propagated by density, and oddness is supplied by complex conjugation; it is used here by [`FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot`](thm.html#FullLevelTate.Datum.exists_injective_equivariant_of_eigenIsoHom_ne_bot) and [`ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense`](thm.html#ModularCurve.exists_blrBlock_of_frobeniusQuadratic_of_dense).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_BostonLenstraRibet_exists_embedding_of_irreducible_of_odd.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem BostonLenstraRibet.exists_embedding_of_irreducible_of_odd {k : Type*} [Field k] {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module k V]
    {ρV : Representation k G V} {ρ : G → Matrix (Fin 2) (Fin 2) k}
    (hρ : ∀ σ τ : G, ρ (σ * τ) = ρ σ * ρ τ)
    (hCH : ∀ σ : G, ρV σ * ρV σ - (ρ σ).trace • ρV σ
      + (ρ σ).det • (1 : Module.End k V) = 0)
    (hirr : ∀ W : Submodule k (Fin 2 → k),
      (∀ g, ∀ v ∈ W, (ρ g).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤)
    {c : G} (hc2 : ρ c * ρ c = 1) (hcdet : (ρ c).det = -1) (h2 : (2 : k) ≠ 0)
    (hV : ∃ v : V, v ≠ 0) :
    ∃ φ : (Fin 2 → k) →ₗ[k] V, Function.Injective φ ∧
      ∀ (σ : G) (v : Fin 2 → k), φ ((ρ σ).mulVec v) = ρV σ (φ v) := by sorry
