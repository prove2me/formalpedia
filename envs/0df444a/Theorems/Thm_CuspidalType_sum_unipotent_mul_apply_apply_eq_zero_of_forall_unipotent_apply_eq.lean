-- Prove2me | Theorems.Thm_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
-- name    : CuspidalType.sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/63fa5e6f-94cb-531d-a331-5fd175c62f6c
-- title:
--   Vanishing of unipotent sums on the image of an intertwiner
-- statement:
--   Let $q$ be a prime and let $\mathrm{GL}_2(\mathbb{Z}/q)$ denote the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$; for $t \in \mathbb{Z}/q$ write $u(t)$ for the unipotent element $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, with inverse $\begin{pmatrix}1&-t\\0&1\end{pmatrix}$. Let $K$ be a commutative ring, $W$ a $K$-module, and $\sigma$ a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $W$ over $K$ with the property that the only $w \in W$ satisfying $\sigma(u(t))w = w$ for all $t \in \mathbb{Z}/q$ is $w = 0$. Let $V'$ be a further $K$-module, $\Phi : \mathrm{GL}_2(\mathbb{Z}/q) \to \mathrm{End}_K(V')$ a monoid homomorphism into the $K$-linear endomorphisms of $V'$, and $f : W \to V'$ a $K$-linear map intertwining the two actions, i.e. $f \circ \sigma(x) = \Phi(x) \circ f$ for every $x \in \mathrm{GL}_2(\mathbb{Z}/q)$. Then for every $w \in W$ and every $g \in \mathrm{GL}_2(\mathbb{Z}/q)$ the endomorphism $\sum_{t \in \mathbb{Z}/q} \Phi(u(t))\,\Phi(g)$ (product in $\mathrm{End}_K(V')$, i.e. composition) annihilates $f(w)$.
--
--   This is the elementary mechanism by which cuspidality — the absence of non-zero vectors fixed by the upper unipotent subgroup — transfers along an equivariant map: the image of $f$ consists of vectors all of whose $\mathrm{GL}_2(\mathbb{Z}/q)$-translates are killed by the sum over the unipotent subgroup. It is used in the construction of linear maps out of Tate modules at full level, in the cases $q = 2$, $q = 3$ and $q \ge 5$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.sum_unipotent_mul_apply_apply_eq_zero_of_forall_unipotent_apply_eq
    (q : ℕ) [Fact q.Prime] (K : Type) [CommRing K] {W : Type} [AddCommGroup W] [Module K W]
    (σ : Representation K (CuspidalType.GL2 q) W)
    (hN : ∀ w : W, (∀ t : ZMod q, σ (CuspidalType.unipotent q t) w = w) → w = 0)
    (V' : Type) [AddCommGroup V'] [Module K V'] (Φ : CuspidalType.GL2 q →* Module.End K V')
    (f : W →ₗ[K] V') (hf : ∀ x : CuspidalType.GL2 q, f ∘ₗ σ x = Φ x ∘ₗ f) :
    ∀ (w : W) (g : CuspidalType.GL2 q), (∑ t : ZMod q, Φ (CuspidalType.unipotent q t) * Φ g) (f w) = 0 := by sorry
