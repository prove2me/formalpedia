-- Prove2me | Theorems.Thm_CuspidalType_IsCuspidalOfType_baseChange
-- name    : CuspidalType.IsCuspidalOfType.baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/4223470b-bbdf-59e8-ac3d-c2ddd596b1cc
-- title:
--   Cuspidality of type θ is preserved by scalar extension
-- statement:
--   Let $q$ be a prime, $K$ a field, $V$ a finite-dimensional $K$-vector space, $\theta \colon (\mathrm{GaloisField}\ q\ 2)^{\times} \to K^{\times}$ a group homomorphism from the units of the field with $q^{2}$ elements, and $\sigma$ a representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$ which is cuspidal of type $\theta$ in the sense of `IsCuspidalOfType`, i.e. $\dim_K V = q-1$; the only vector fixed by $\sigma(\mathrm{unipotent}\ q\ t)$, the matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, for all $t \in \mathbb{Z}/q$ is $0$; $\sigma$ sends every scalar matrix $\mathrm{scalarElem}\ q\ c$, $c \in (\mathbb{Z}/q)^{\times}$, to the identity; and for every $\alpha \in (\mathrm{GaloisField}\ q\ 2)^{\times}$ the characteristic polynomial of $\sigma(\mathrm{torus}\ q\ \alpha)$, where $\mathrm{torus}$ realises multiplication by $\alpha$ on $\mathrm{GaloisField}\ q\ 2$ as a matrix in the basis `quadBasis q`, satisfies $\mathrm{charpoly}(\sigma(\mathrm{torus}\ q\ \alpha)) \cdot (X - \theta(\alpha))(X - \theta(\alpha)^{-1}) = \mathrm{charpoly}(\mathrm{ind}\ q\ K\,(\mathrm{torus}\ q\ \alpha))$, with $\mathrm{ind}\ q\ K$ the permutation representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on finitely supported $K$-valued functions on `ProjLine q`. Then for every field $K'$ that is a $K$-algebra, the representation $g \mapsto \sigma(g) \otimes \mathrm{id}$ of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $K' \otimes_K V$, obtained by composing $\sigma$ with `Module.End.baseChangeHom`, is cuspidal of type $\theta$ followed by the map $K^{\times} \to K'^{\times}$ induced by $K \to K'$.
--
--   This is the statement that the notion of a cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ of type $\theta$, as axiomatised by the four conditions of `IsCuspidalOfType`, is stable under extension of the coefficient field. It is used to pass to a larger (for instance perfect) coefficient field in [`DrinfeldCurve.slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField`](thm.html#DrinfeldCurve.slEquivariant_quadratic_of_isCuspidalOfType_of_perfectField).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_IsCuspidalOfType_baseChange.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

namespace CuspidalType

theorem IsCuspidalOfType.baseChange
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {θ : (GaloisField q 2)ˣ →* Kˣ} {σ : Representation K (GL2 q) V} (h : IsCuspidalOfType θ σ)
    (K' : Type*) [Field K'] [Algebra K K'] :
    IsCuspidalOfType ((Units.map (algebraMap K K').toMonoidHom).comp θ)
      ((Module.End.baseChangeHom K K' V : Module.End K V →* Module.End K' (K' ⊗[K] V)).comp σ) := by sorry
