-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
-- name    : AutomorphicForm.exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/372849ce-284b-519a-a46b-46f4dd0d5eaa
-- title:
--   Twisted centraliser of the scalars in adelic GL₂
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and a $K$-algebra, let $\sigma$ be an automorphism of $L$ as a $K$-algebra, and let $D$ be a datum of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a monoid homomorphism $\mathrm{act}$ from the group of $K$-algebra automorphisms of $L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$ (formed with respect to $\mathcal{O}_L$), such that each $\mathrm{act}(g)$ is continuous and satisfies $\mathrm{act}(g)(x) = g(x)$ on principal adeles. Write $G = \mathrm{GL}_2(\mathbb{A}_L)$ and let $\sigma_{\mathbb{A}} \colon G \to G$ be the group homomorphism obtained by applying the ring automorphism $\mathrm{act}(\sigma)$ entrywise. The assertion is that there exists a subset $C \subseteq G$ which is compact and contained in the centre of $G$, with the following property: for every $g \in G$ such that $g^{-1}\,\sigma_{\mathbb{A}}(g)$ lies in the centre of $G$, there are $h, c \in G$ and $l \in L^{\times}$ with $\sigma_{\mathbb{A}}(h) = h$, with $c \in C$, and with $g = h \cdot c \cdot \iota(l \cdot 1_2)$, where $\iota \colon \mathrm{GL}_2(L) \to G$ is the entrywise map induced by $L \to \mathbb{A}_L$ and $l \cdot 1_2$ is the scalar matrix with entry $l$.
--
--   This is the structure theorem for the twisted centraliser of the scalars, $\{g \in G : g^{-1}\sigma_{\mathbb{A}}(g) \in Z(G)\} = G^{\sigma_{\mathbb{A}}} \cdot C \cdot \iota(L^{\times})$, with $C$ compact and central; it rests on Hilbert's Theorem 90 for ideles together with compactness of the norm-one idele classes. It is used in the measure-theoretic estimate [`AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center`](thm.html#AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center), which bounds Haar measures of preimages over the fixed locus of $\sigma_{\mathbb{A}}$ modulo the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.exists_isCompact_subset_center_forall_eq_mul_mul_scalar_of_inv_mul_sigmaAdelicAct_mem_center
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    ∃ C : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L), IsCompact C ∧
      C ⊆ (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) :
        Set (AutomorphicForm.AdelicGL2 (𝓞 L) L)) ∧
      ∀ g : AutomorphicForm.AdelicGL2 (𝓞 L) L,
        g⁻¹ * AutomorphicForm.sigmaAdelicAct K L D σ g ∈
            Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L) →
          ∃ (h c : AutomorphicForm.AdelicGL2 (𝓞 L) L) (l : Lˣ),
            AutomorphicForm.sigmaAdelicAct K L D σ h = h ∧ c ∈ C ∧
              g = h * c * AutomorphicForm.globalPoints (𝓞 L) L
                (Matrix.GeneralLinearGroup.scalar (Fin 2) l) := by sorry
