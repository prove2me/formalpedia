-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
-- name    : AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/81e60056-875d-53c4-aa54-6ab274568c49
-- title:
--   Uniform finite volume bound on determinant slabs for σ-fixed points
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $D$ be a datum of type [`M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L`](def/M4aHerbrand_IdeleClassVocab.html#L28), that is, a monoid homomorphism from the group of $K$-algebra automorphisms of $L$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$, compatible with the structure map $L \to \mathbb{A}_L$ and continuous in each element. Write $G = \mathrm{GL}_2(\mathbb{A}_L)$, endowed with a measurable structure which is the Borel structure of its topology, and let $\sigma_{\mathbb{A}}$ be the endomorphism of $G$ obtained by applying the ring automorphism $D.\mathrm{act}\,\sigma$ entrywise. Let $\mu$ be a Haar measure on the equaliser subgroup $G^{\sigma} = \{g \in G : \sigma_{\mathbb{A}}(g) = g\}$, and let $a, b$ be reals with $a > 0$. Then there is $V_0 \in [0,\infty]$ with $V_0 < \infty$ such that for every measurable $E \subseteq G$ contained in the slab $\{g : \|\det g\| \in [a,b]\}$, where $\|x\| = \mathrm{distribHaarChar}(\mathbb{A}_L)(x)$ viewed as a real number, and such that for all $s \neq s'$ in $\mathrm{GL}_2(L)$ fixed entrywise by $\sigma$ the intersection of the pointwise translates $\iota(s) \cdot E$ and $\iota(s') \cdot E$ has $\mu$-null preimage in $G^{\sigma}$, where $\iota \colon \mathrm{GL}_2(L) \to G$ is the entrywise map induced by $L \to \mathbb{A}_L$, one has $\mu(\iota^{-1}$-free preimage $E \cap G^{\sigma}) \le V_0$, the preimage being taken along the inclusion of $G^{\sigma}$ in $G$. The bound $V_0$ depends only on $K, L, \sigma, D, \mu, a, b$ and not on $E$.
--
--   This is the finiteness of covolume (Godement's criterion in the guise used for base change) for the $\sigma$-fixed adelic group, in the quantitative form of a single finite bound valid for all measurable sets whose translates by the $\sigma$-fixed rational points are almost disjoint and whose determinant norms lie in a fixed slab. It is used in the corresponding statement for translates by the centre, [`AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center`](thm.html#AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_center).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open scoped ENNReal Pointwise

theorem AutomorphicForm.exists_lt_top_forall_measure_preimage_le_of_isHaarMeasure_eqLocus_sigmaAdelicAct_id
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    [MeasurableSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    [BorelSpace (AutomorphicForm.AdelicGL2 (𝓞 L) L)]
    (μ : Measure (MonoidHom.eqLocus (AutomorphicForm.sigmaAdelicAct K L D σ)
        (MonoidHom.id (AutomorphicForm.AdelicGL2 (𝓞 L) L))))
    [μ.IsHaarMeasure] (a b : ℝ) (ha : 0 < a) :
    ∃ V₀ : ℝ≥0∞, V₀ < ⊤ ∧
      ∀ E : Set (AutomorphicForm.AdelicGL2 (𝓞 L) L),
        E ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        MeasurableSet E →
        (∀ s s' : GL (Fin 2) L,
          Matrix.GeneralLinearGroup.map (σ : L →+* L) s = s →
          Matrix.GeneralLinearGroup.map (σ : L →+* L) s' = s' →
          s ≠ s' →
            μ (Subtype.val ⁻¹'
              (AutomorphicForm.globalPoints (𝓞 L) L s • E ∩
                AutomorphicForm.globalPoints (𝓞 L) L s' • E)) = 0) →
        μ (Subtype.val ⁻¹' E) ≤ V₀ := by sorry
