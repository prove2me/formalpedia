-- Prove2me | Theorems.Thm_CuspidalType_IsCuspidalOfType_dual
-- name    : CuspidalType.IsCuspidalOfType.dual
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/ade3f330-9f7a-54de-809a-3ff87e7b5d12
-- title:
--   The dual of a cuspidal type is cuspidal of the same type
-- statement:
--   Let $q$ be a prime, $K$ a field of characteristic zero, $\theta\colon \mathbb{F}_{q^2}^{\times}\to K^{\times}$ a group homomorphism (with $\mathbb{F}_{q^2}$ realised as `GaloisField q 2`), and $V$ a finite-dimensional $K$-vector space carrying a representation $\rho$ of $\mathrm{GL}_2(\mathbb{Z}/q)$. Assume $\rho$ is cuspidal of type $\theta$ in the sense of [`CuspidalType.IsCuspidalOfType`](def/CuspidalType_IsCuspidalOfType.html#L100), that is: $\dim_K V = q-1$; every $v\in V$ fixed by all the unipotent matrices $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, $t\in\mathbb{Z}/q$, vanishes; every scalar matrix $c\cdot 1$, $c\in(\mathbb{Z}/q)^{\times}$, acts as the identity; and for every $\alpha\in\mathbb{F}_{q^2}^{\times}$, writing $\mathrm{torus}\,\alpha$ for the image of $\alpha$ in $\mathrm{GL}_2(\mathbb{Z}/q)$ under multiplication by $\alpha$ on $\mathbb{F}_{q^2}$ read in the basis `quadBasis q`, one has $$\mathrm{charpoly}(\rho(\mathrm{torus}\,\alpha))\cdot\bigl(X-\theta(\alpha)\bigr)\bigl(X-\theta(\alpha)^{-1}\bigr)=\mathrm{charpoly}\bigl(\mathrm{ind}\,q\,K\,(\mathrm{torus}\,\alpha)\bigr),$$ where `ind q K` is the reference representation used in the definition. The conclusion is that the dual representation `ρ.dual`, sending $g$ to the transpose of $\rho(g^{-1})$ on $\mathrm{Hom}_K(V,K)$, is again cuspidal of type $\theta$, for the same character $\theta$.
--
--   This is the statement that the contragredient of a cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ of type $\theta$ is cuspidal of the same type, in the axiomatic form in which cuspidal types are characterised here by dimension, absence of unipotent invariants, triviality of the centre and a characteristic-polynomial identity on the non-split torus. It is used in the construction of a Hecke eigenvalue homomorphism acting on the Tate module of the Jacobian of the full-level modular curve, where the cuspidal type attached to a representation and to its dual must be matched.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_IsCuspidalOfType_dual.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.RepresentationTheory.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspidalType.IsCuspidalOfType.dual
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [CharZero K] {θ : (GaloisField q 2)ˣ →* Kˣ}
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {ρ : Representation K (CuspidalType.GL2 q) V}
    (h : CuspidalType.IsCuspidalOfType θ ρ) :
    CuspidalType.IsCuspidalOfType θ ρ.dual := by sorry
