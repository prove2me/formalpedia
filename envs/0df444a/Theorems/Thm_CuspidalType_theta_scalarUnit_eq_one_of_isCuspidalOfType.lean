-- Prove2me | Theorems.Thm_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType
-- name    : CuspidalType.theta_scalarUnit_eq_one_of_isCuspidalOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/23b07fb7-ff8e-5868-830e-aecafaedbb34
-- title:
--   A cuspidal type is trivial on 𝔽_q^×
-- statement:
--   Let $q$ be a prime, $K$ a field and $V$ a finite-dimensional $K$-vector space. Let $\theta\colon \mathbb{F}_{q^2}^{\times}\to K^{\times}$ be a group homomorphism, where $\mathbb{F}_{q^2}$ is realised as `GaloisField q 2`, and let $\rho$ be a $K$-linear representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$. Assume `IsCuspidalOfType θ ρ`, that is: $\dim_K V = q-1$; the only vector fixed by all the upper unipotent matrices $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $t \in \mathbb{Z}/q$, is $0$; $\rho$ sends every scalar matrix $\mathrm{diag}(c,c)$ with $c \in (\mathbb{Z}/q)^{\times}$ to the identity; and for every $\alpha \in \mathbb{F}_{q^2}^{\times}$ the characteristic polynomial of $\rho$ at the non-split torus element $\alpha$ (multiplication by $\alpha$ on $\mathbb{F}_{q^2}$ written in the basis `quadBasis q`), multiplied by $(X-\theta(\alpha))(X-\theta(\alpha)^{-1})$, equals the characteristic polynomial of that same group element acting in the representation `ind q K` on the projective line. Then for every $c \in (\mathbb{Z}/q)^{\times}$ one has $\theta(c) = 1$, where $c$ is mapped into $\mathbb{F}_{q^2}^{\times}$ by the units map of the structure morphism $\mathbb{Z}/q \to \mathbb{F}_{q^2}$.
--
--   This records the standard fact that the character $\theta$ cutting out a cuspidal type of $\mathrm{GL}_2(\mathbb{F}_q)$ is trivial on the scalars $\mathbb{F}_q^{\times} \subset \mathbb{F}_{q^2}^{\times}$, a consequence of the centre acting trivially in the type. It is used in the determination of the order of $\theta$ on $\mathbb{F}_{q^2}^{\times}$ and in the vanishing of the twisted intertwining map for cuspidal types in the Drinfeld curve computation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_theta_scalarUnit_eq_one_of_isCuspidalOfType.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.theta_scalarUnit_eq_one_of_isCuspidalOfType {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V}
    (h : IsCuspidalOfType θ ρ) (c : (ZMod q)ˣ) :
    θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by sorry
