-- Prove2me | Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- name    : AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/37d5e002-0fac-5966-9696-993cf23a23d6
-- title:
--   Unimodularity of the σ-twisted centraliser modulo the centre
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $D$ be a datum of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a monoid homomorphism from $L \simeq_{\mathrm{alg}[K]} L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$, compatible with the structure map $L \to \mathbb{A}_L$ and continuous for each automorphism. Put $G = \mathrm{GL}_2(\mathbb{A}_L)$, equipped with a measurable structure which is the Borel structure of its topology, and let $\sigma_{\mathbb{A}} =$ [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) be the endomorphism of $G$ obtained by applying the ring automorphism $D.\mathrm{act}\,\sigma$ entrywise. Let $Z$ be the centre of $G$ and consider the subgroup $G_1$ of $G$ on which the two homomorphisms $g \mapsto \sigma_{\mathbb{A}}(g)Z$ and $g \mapsto gZ$ into $G/Z$ agree, i.e. $G_1 = \{g : g^{-1}\sigma_{\mathbb{A}}(g) \in Z\}$. The assertion is that every Haar measure $\mu_H$ on $G_1$ is right invariant.
--
--   This is the unimodularity of the $\sigma$-twisted centraliser of the scalars modulo the centre in $\mathrm{GL}_2$ over the adeles, the group on which twisted trace formula and base-change arguments for $\mathrm{GL}(2)$ are set up. It is used to supply the right-invariance hypothesis needed for quotient-measure (Weil formula) computations on $G/G_1$, and is cited in the estimates [`AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter`](thm.html#AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter) and [`AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center`](thm.html#AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μH : Measure (MonoidHom.eqLocus
        ((QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))).comp
          (AutomorphicForm.sigmaAdelicAct K L D σ))
        (QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))))
    [μH.IsHaarMeasure] : μH.IsMulRightInvariant := by sorry
