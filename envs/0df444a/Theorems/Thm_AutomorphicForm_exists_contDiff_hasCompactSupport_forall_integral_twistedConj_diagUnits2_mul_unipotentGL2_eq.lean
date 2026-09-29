-- Prove2me | Theorems.Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
-- name    : AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/eb665fb2-3b65-52a4-ba1c-1260accddcd3
-- title:
--   Smoothness of the twisted K-average of an archimedean test factor
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite Galois, let $\sigma$ be a $K$-automorphism of $L$ such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$, $\iota_L$ for the composite of `archIdent` $: E \to \mathbb{A}_{L,\infty}$ with the identification of $\mathbb{A}_{L,\infty}$ with the mixed space of $L$, and $\mathbf{K}_E \le GL_2(E)$ for the intersection, over the infinite places $w$ of $L$, of the preimages under $GL_2(E) \to GL_2(L_w)$ (induced by `archIdent` followed by evaluation at $w$) of the set of $k \in GL_2(L_w)$ with $\lVert \det k \rVert = 1$ and $\lVert x k_{00} + y k_{10}\rVert^2 + \lVert x k_{01} + y k_{11} \rVert^2 = \lVert x \rVert^2 + \lVert y \rVert^2$ for all $x, y \in L_w$; $\mathbf{K}_E$ carries its Borel $\sigma$-algebra and a Haar measure $\kappa$. Let $\varphi_a : GL_2(\mathbb{A}_{L,\infty}) \to \mathbb{C}$ satisfy `IsArchTestFactor`: it has compact support and is of the form $g \mapsto \Phi_0$ of the matrix of entries of $g$ read in the mixed space of $L$, for some $\Phi_0$ smooth ($C^\infty$ over $\mathbb{R}$) on $2 \times 2$ matrices over that mixed space. Then there exists $\Phi$ on triples of elements of the mixed space of $L$, smooth over $\mathbb{R}$ and with compact support, such that (i) there is a compact $C \subseteq E^\times \times E^\times$ with the property that for every $p$ in the closed support of $\Phi$ one has $p_0 = \iota_L(q_1)$ and $p_1 = \iota_L(q_2)$ for some $(q_1,q_2) \in C$, and (ii) for all $d_1, d_2 \in E^\times$ and all $y \in E$, $$\int_{\mathbf{K}_E} \varphi_a\bigl(k^{-1}\, \mathrm{diag}(d_1,d_2)\, \begin{pmatrix} 1 & y \\ 0 & 1\end{pmatrix}\, \sigma(k)\bigr)\, d\kappa(k) = \Phi(\iota_L d_1, \iota_L d_2, \iota_L y),$$ where the argument is transported to $GL_2(\mathbb{A}_{L,\infty})$ by `archIdentGL` and $\sigma$ acts on $GL_2(E)$ entrywise through $\sigma \otimes \mathrm{id}$.
--
--   This is the archimedean pre-average kernel for the twisted orbital integrals occurring in the base-change comparison: the $\mathbf{K}_E$-average of an archimedean test factor along $\mathrm{diag}(d_1,d_2)\,n(y)$ under $\sigma$-twisted conjugation is realised as a fixed smooth compactly supported function of the three mixed-space coordinates $(\iota_L d_1, \iota_L d_2, \iota_L y)$, with the support controlled by a compact set of pairs of units. It feeds the subsequent evaluation of the twisted weighted archimedean contribution, where the logarithmic terms attached to the infinite places are extracted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_contDiff_hasCompactSupport_forall_integral_twistedConj_diagUnits2_mul_unipotentGL2_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (φa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (hφa : AutomorphicForm.IsArchTestFactor L φa)
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ Φ : (Fin 3 → NumberField.mixedEmbedding.mixedSpace L) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
      (∃ C : Set ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ), IsCompact C ∧
        ∀ p ∈ tsupport Φ, ∃ q ∈ C,
          p 0 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.1 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K))) ∧
          p 1 = NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L ((q.2 : (L ⊗[K] InfiniteAdeleRing K)ˣ) : (L ⊗[K] InfiniteAdeleRing K)))) ∧
      ∀ (d₁ d₂ : (L ⊗[K] InfiniteAdeleRing K)ˣ) (y : (L ⊗[K] InfiniteAdeleRing K)),
        @integral _ ℂ _ _ (borel _) κ (fun k =>
            φa (AutomorphicForm.archIdentGL K L
              ((k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))⁻¹ * (diagUnits2 d₁ d₂ * AutomorphicForm.unipotentGL2 y) *
                AutomorphicForm.sigmaGL K L (InfiniteAdeleRing K) σ (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) =
          Φ ![NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (d₁ : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (d₂ : (L ⊗[K] InfiniteAdeleRing K))), NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y)] := by sorry
