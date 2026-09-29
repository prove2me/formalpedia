-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- name    : AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/06e9242f-f4f8-59d1-98b1-e6ad2546ff2c
-- title:
--   Uniform finite volume bound on determinant slabs in the twisted locus
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, let $\sigma : L \simeq_{\mathrm{alg}[K]} L$ be a $K$-algebra automorphism of $L$, and let $D$ be a datum [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), i.e. a monoid homomorphism $\mathrm{act}$ from $L\simeq_{\mathrm{alg}[K]}L$ to the ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, each $\mathrm{act}\,g$ continuous and satisfying $\mathrm{act}\,g(\iota x) = \iota(g x)$ for $x \in L$, where $\iota$ is the structure map $L \to \mathbb{A}_L$. Write $G = \mathrm{GL}_2(\mathbb{A}_L)$, equipped with a measurable space structure that is its Borel $\sigma$-algebra, and let $\sigma_{\mathbb{A}} =$ [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14) be the endomorphism of $G$ obtained by applying the ring automorphism $\mathrm{act}\,\sigma$ entrywise. Let $H$ be the equaliser subgroup of the two homomorphisms $G \to G/Z(G)$ given by $g \mapsto \sigma_{\mathbb{A}}(g)Z(G)$ and $g \mapsto gZ(G)$, that is $H = \{g \in G : g^{-1}\sigma_{\mathbb{A}}(g) \in Z(G)\}$, and let $\mu_H$ be a Haar measure on $H$. Fix reals $a, b$ with $a > 0$. The assertion is that there exists $V_0 \in [0,\infty]$ with $V_0 < \infty$ such that for every measurable $E \subseteq G$ contained in the slab $\{g : \|\det g\| \in [a,b]\}$, where $\|\cdot\| =$ [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) is the value of the distributive Haar character of $\mathbb{A}_L$ on an idele, the following implication holds: if for all $s, s' \in \mathrm{GL}_2(L)$ with $s \ne s'$ such that $s^{-1}\cdot \sigma(s)$ and $s'^{-1}\cdot\sigma(s')$ (entrywise application of $\sigma$) are scalar matrices $u\cdot 1$ for units $u$ of $L$, the set $(\iota_* s)\cdot E \cap (\iota_* s')\cdot E$ has $\mu_H$-measure zero after pulling back along the inclusion $H \hookrightarrow G$, where $\iota_*$ denotes [`AutomorphicForm.globalPoints (𝓞 L) L`](def/AutomorphicForm_AdelicLsXi.html#L15), the entrywise embedding $\mathrm{GL}_2(L) \to G$, then $\mu_H$ of the preimage of $E$ in $H$ is at most $V_0$. In particular $V_0$ does not depend on $E$.
--
--   This is the finiteness-of-covolume bound, in the style of Godement's criterion and the Borel–Harish-Chandra finiteness theorems, for the twisted locus $H = \{g : g^{-1}\sigma_{\mathbb{A}}(g) \in Z(G)\}$ inside $\mathrm{GL}_2(\mathbb{A}_L)$: any $\mu_H$-almost disjoint packing of translates by the rational points $s$ with $s^{-1}\sigma(s)$ scalar, of a determinant slab $a \le \|\det\| \le b$, is bounded by one finite constant. It is used by [`AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter`](thm.html#AutomorphicForm.adelicGLHaar_inter_setOf_inv_mul_sigmaAdelicAct_mem_center_mul_lt_top_of_forall_smul_inter) to obtain finiteness of the volume of such sets.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal Pointwise

theorem AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μH : Measure (MonoidHom.eqLocus
        ((QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L))).comp
          (AutomorphicForm.sigmaAdelicAct K L D σ))
        (QuotientGroup.mk' (Subgroup.center (AutomorphicForm.AdelicGL2 (𝓞 L) L)))))
    [μH.IsHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    ∃ V₀ : ℝ≥0∞, V₀ < ⊤ ∧
      ∀ E : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L),
        E ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        MeasurableSet E →
        (∀ s s' : GL (Fin 2) L,
          (∃ u : Lˣ, s⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s =
            Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
          (∃ u : Lˣ, s'⁻¹ * Matrix.GeneralLinearGroup.map (σ : L →+* L) s' =
            Matrix.GeneralLinearGroup.scalar (Fin 2) u) →
          s ≠ s' →
            μH (Subtype.val ⁻¹'
              (AutomorphicForm.globalPoints (𝓞 L) L s • E ∩
                AutomorphicForm.globalPoints (𝓞 L) L s' • E)) = 0) →
        μH (Subtype.val ⁻¹' E) ≤ V₀ := by sorry
