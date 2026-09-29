-- Prove2me | Theorems.Thm_CuspidalType_IsCuspidalOfType_of_linearEquiv
-- name    : CuspidalType.IsCuspidalOfType.of_linearEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/f67ad880-ac87-57da-881c-31db6f60ad35
-- title:
--   Cuspidality of type θ transports along equivariant isomorphisms
-- statement:
--   Let $q$ be a prime, $K$ a field, and $V$, $V'$ finite-dimensional $K$-vector spaces. Let $\theta\colon \mathbb{F}_{q^2}^{\times}\to K^{\times}$ be a group homomorphism (the units of `GaloisField q 2` to those of $K$), and let $\rho$, $\rho'$ be $K$-linear representations of `GL2 q`, the general linear group of $2\times 2$ matrices over $\mathbb{Z}/q$, on $V$ and $V'$ respectively. Assume `IsCuspidalOfType θ ρ`, that is: $\dim_K V = q-1$ (truncated subtraction in $\mathbb{N}$); every $v\in V$ fixed by $\rho(\mathrm{unipotent}(t))$ for all $t\in\mathbb{Z}/q$, where $\mathrm{unipotent}(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix}$, is zero; $\rho$ sends every scalar matrix $c\cdot I$, $c\in(\mathbb{Z}/q)^{\times}$, to the identity; and for every $\alpha\in\mathbb{F}_{q^2}^{\times}$ the characteristic polynomial of $\rho(\mathrm{torus}(\alpha))$, where $\mathrm{torus}(\alpha)$ is the matrix of multiplication by $\alpha$ on $\mathbb{F}_{q^2}$ in the basis `quadBasis q`, times $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$ equals the characteristic polynomial of `ind q K (torus q α)`. Assume further given a $K$-linear isomorphism $e\colon V\simeq V'$ with $e(\rho(g)v)=\rho'(g)(e\,v)$ for all $g$ and $v$. Then `IsCuspidalOfType θ ρ'` holds.
--
--   This is the invariance of the property 'cuspidal of type $\theta$' for representations of $\mathrm{GL}_2(\mathbb{F}_q)$ under equivariant isomorphism, allowing the type of a representation to be read off from any model of it. It is used where a cuspidal type is produced for one model of a mod-$q$ or local representation and needed for another, notably in the construction of cuspidal types from newforms and from local new vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_IsCuspidalOfType_of_linearEquiv.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.of_linearEquiv {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {V' : Type*} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} {ρ' : Representation K (GL2 q) V'}
    (h : IsCuspidalOfType θ ρ) (e : V ≃ₗ[K] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    IsCuspidalOfType θ ρ' := by sorry
