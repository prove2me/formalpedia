-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
-- name    : AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/38c1a078-4149-505f-a8f2-77a9e4169173
-- title:
--   Properness modulo the centre of the twisted orbit map on GL₂(A_L)
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $D$ be a datum of idele Galois descent for $\mathcal{O}_L$, $K$, $L$: a monoid homomorphism $g \mapsto D.\mathrm{act}\,g$ from $\mathrm{Aut}_K(L)$ to the ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that each $D.\mathrm{act}\,g$ is continuous and agrees with $g$ on principal adeles, i.e. $D.\mathrm{act}\,g\,(\iota x) = \iota(g x)$ for $x \in L$. Write $G = \mathrm{GL}_2(\mathbb{A}_L)$ and let $\sigma_{\mathbb{A}} =$ `sigmaAdelicAct K L D σ` be the group endomorphism of $G$ obtained by applying the ring automorphism $D.\mathrm{act}\,\sigma$ entrywise. Let $C \subseteq G$ be compact. The assertion is that there exists a compact $C' \subseteq G$ with the following property: for every $y \in G$ such that $y^{-1}\sigma_{\mathbb{A}}(y)$ lies in the pointwise product of the underlying set of the centre $Z$ of $G$ with $C$, there are $g, k \in G$ with $g^{-1}\sigma_{\mathbb{A}}(g) \in Z$, with $k \in C'$, and with $y = g k$.
--
--   This is the properness, modulo the centre, of the twisted orbit map $y \mapsto y^{-1}\sigma_{\mathbb{A}}(y)$ at the identity: preimages of sets $Z \cdot C$ with $C$ compact are contained in (twisted centraliser of the identity modulo the centre) times a fixed compact set. It is used to show that the twisted orbital integral at the identity of a compactly supported function has compact support modulo the twisted centraliser, and it feeds into the finiteness of the integral of the twisted kernel for the identity family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped Pointwise

theorem AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) (hC : IsCompact C) :
    ∃ C' : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C' ∧
      ∀ y : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        y⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ y ∈
            (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
              Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) * C →
          ∃ g k : AutomorphicForm.AdelicGL2 (𝓞 L) L,
            g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
                Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) ∧
              k ∈ C' ∧ y = g * k := by sorry
