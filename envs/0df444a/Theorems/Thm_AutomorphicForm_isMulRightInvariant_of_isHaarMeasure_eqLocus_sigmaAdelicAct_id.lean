-- Prove2me | Theorems.Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
-- name    : AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/d0708db4-1ebf-5c06-aa18-b0637b5bbf33
-- title:
--   Unimodularity of the σ-fixed subgroup of GL₂(A_L)
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and a $K$-algebra, and let $\sigma$ be a $K$-algebra automorphism of $L$. Let $D$ be an idele Galois descent datum for $\mathcal{O}_L$, $K$, $L$: a monoid homomorphism $D.\mathrm{act}$ from the group of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that each $D.\mathrm{act}\,g$ fixes principal adeles in the sense that it carries the image of $x \in L$ to the image of $g x$, and such that each $D.\mathrm{act}\,g$ is continuous. Write $G =$ [`AutomorphicForm.AdelicGL2 (𝓞 L) L`](def/AutomorphicForm_AdelicLsXi.html#L12) for $\mathrm{GL}_2(\mathbb{A}_L)$, equipped with a measurable space structure which is the Borel structure of its topology, and let $\sigma_{\mathbb{A}} =$ [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) be the endomorphism of $G$ obtained by applying the ring homomorphism $D.\mathrm{act}\,\sigma$ entrywise. Let $\mu$ be a left Haar measure (in Mathlib's sense: left invariant, regular, finite on compacts and positive on nonempty open sets) on the subgroup $\{g \in G : \sigma_{\mathbb{A}}(g) = g\}$, the locus where $\sigma_{\mathbb{A}}$ agrees with the identity homomorphism of $G$. Then $\mu$ is also right invariant.
--
--   This is the unimodularity of the $\sigma$-fixed subgroup of $\mathrm{GL}_2$ of the adeles, which via uniqueness of the descent datum is $\mathrm{GL}_2$ of the adeles of the fixed field; it rests on the right invariance of the adelic Haar measure [`NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar`](thm.html#NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar) together with uniqueness of Haar measure, for which second countability of $\mathrm{GL}_2(\mathbb{A}_L)$ is recorded. It serves the integration theory of automorphic forms on such fixed subgroups, and is used for the corresponding statements over the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem AutomorphicForm.isMulRightInvariant_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μ : Measure (MonoidHom.eqLocus (AutomorphicForm.sigmaAdelicAct K L D σ)
        (MonoidHom.id (AutomorphicForm.AdelicGL2 (𝓞 L) L))))
    [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by sorry
