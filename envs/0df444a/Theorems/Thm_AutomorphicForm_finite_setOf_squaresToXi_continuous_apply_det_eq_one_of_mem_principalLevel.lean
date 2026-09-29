-- Prove2me | Theorems.Thm_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
-- name    : AutomorphicForm.finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/b85b005c-228c-5cad-aa8a-22d1bc4de425
-- title:
--   Finiteness of continuous idele class characters of square ξ and level N
-- statement:
--   Let $K$ be a number field (a field with a `NumberField` instance), let $\xi$ be a monoid homomorphism from the full subgroup $\top$ of the unit group $(\mathbb{A}_K)^\times$ of the adele ring of $\mathcal{O}_K$ in $K$ to $\mathbb{C}^\times$, and let $N$ be a nonzero ideal of $\mathcal{O}_K$. The assertion is that the following set of monoid homomorphisms $\chi \colon (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ is finite: those $\chi$ satisfying simultaneously (i) [`AutomorphicForm.SquaresToXi`](def/AutomorphicForm_AdelicLsXi.html#L27) for $Z = \top$ and $\xi$, i.e. $\chi(z)^2 = \xi(z)$ for every idele unit $z$; (ii) $\chi(z) = 1$ for every $z$ in the range of the map on units induced by the structure map $K \to \mathbb{A}_K$, i.e. triviality on the principal ideles; (iii) continuity of $z \mapsto \chi(z)$ viewed as a map into $\mathbb{C}$; and (iv) $\chi(\det u) = 1$ for every $u$ in the intersection of `principalLevel (𝓞 K) K N` with `finiteAdelicGL2Subgroup K`, where the former is the intersection of `levelOne (𝓞 K) K N` — the preimage under the finite-part homomorphism `glFin` of the level-$N$ subgroup `finiteLevelOne` — with its image under conjugation by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$, and the latter is the kernel of [`NumberField.AdelicLevel.glArch`](def/NumberField_AdelicLevel.html#L191), i.e. the elements of $GL_2(\mathbb{A}_K)$ with trivial archimedean component.
--
--   This is the finiteness, for fixed square $\xi$ and fixed level $N$, of the continuous idele class characters whose associated one-dimensional representations $\chi \circ \det$ can occur in the residual part of the space of automorphic forms on $GL_2$ of level $N$; it rests on the compactness of the norm-one idele class group. It is used in the constructions of residual projections and in the computation of the corresponding integrals of convolution operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel.lean

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem AutomorphicForm.finite_setOf_squaresToXi_continuous_apply_det_eq_one_of_mem_principalLevel
    (K : Type) [Field K] [NumberField K]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 K)) (hN0 : N ≠ ⊥) :
    {χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ |
        AutomorphicForm.SquaresToXi (𝓞 K) K ⊤ ξ χ ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range → χ z = 1) ∧
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ z : ℂˣ) : ℂ)) ∧
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
          χ (Matrix.GeneralLinearGroup.det u) = 1}.Finite := by sorry
