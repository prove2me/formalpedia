-- Prove2me | Theorems.Thm_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot
-- name    : CuspidalType.IsCuspidalOfType.toSubmodule_eq_top_of_ne_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/32b488c9-9877-50d1-bb8f-9d0a2a11b29d
-- title:
--   Cuspidal representations of a given type are irreducible
-- statement:
--   Let $q$ be a prime, $K$ a field, and $V$ a finite-dimensional $K$-vector space. Let $\theta : \mathbb{F}_{q^2}^{\times} \to K^{\times}$ be a character, written as a monoid homomorphism on the units of `GaloisField q 2`, and let $\rho$ be a $K$-linear representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$ which is cuspidal of type $\theta$ in the sense of `IsCuspidalOfType`, i.e.: $\dim_K V = q - 1$; no non-zero vector of $V$ is fixed by all the upper unipotent matrices $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $t \in \mathbb{Z}/q$; every scalar matrix acts as the identity; and for every $\alpha \in \mathbb{F}_{q^2}^{\times}$ the characteristic polynomial of $\rho$ at the image `torus q α` of $\alpha$ under multiplication on $\mathbb{F}_{q^2}$ viewed in $\mathrm{GL}_2(\mathbb{Z}/q)$, multiplied by $(X - \theta(\alpha))(X - \theta(\alpha)^{-1})$, equals the characteristic polynomial of `ind q K (torus q α)`. Assume further that $q \neq 0$ and $q - 1 \neq 0$ in $K$. Then for every subrepresentation $W$ of $\rho$ whose underlying submodule is non-zero, that submodule is all of $V$.
--
--   This is the irreducibility of a cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ of prescribed type $\theta$, under the hypothesis that $q$ and $q-1$ are invertible in the coefficient field. It is used to identify such representations up to isomorphism, to establish irreducibility of the $\mathrm{GL}_2$-reduction attached to a newform, and in the vanishing of intertwining maps for twists over algebraically closed coefficient fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_IsCuspidalOfType_toSubmodule_eq_top_of_ne_bot.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.toSubmodule_eq_top_of_ne_bot {q : ℕ} [Fact q.Prime] {K : Type*} [Field K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {ρ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ ρ)
    (hq : (q : K) ≠ 0) (hq1 : ((q : K) - 1 ≠ 0)) (W : Subrepresentation ρ) (hW : W.toSubmodule ≠ ⊥) :
    W.toSubmodule = ⊤ := by sorry
