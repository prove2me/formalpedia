-- Prove2me | Theorems.Thm_AutomorphicForm_exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
-- name    : AutomorphicForm.exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/8ef16361-7ac8-537c-ad73-8fddd1fc017c
-- title:
--   Iwasawa integration formula on GL₂(L ⊗_K K_∞)
-- statement:
--   Let $K \subseteq L$ be number fields with $L$ finite over $K$, and write $E = L \otimes_K \mathrm{InfiniteAdeleRing}\,K$. Fix: a Haar measure $\nu$ on $\mathrm{GL}_2(E)$ for the Borel $\sigma$-algebra [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57) of the topology of $\mathrm{GL}_2(E)$; an additive Haar measure $\mathrm{lam}$ on $E$ and a Haar measure $\rho$ on $E^\times$, each for a Borel measurable structure; and a Haar measure $\kappa$, for the Borel $\sigma$-algebra, on the subgroup $\mathbf{K}$ of $\mathrm{GL}_2(E)$ obtained by pulling back along the map [`AutomorphicForm.archIdentGL`](def/AutomorphicForm_TwistedOrbital.html#L424) $K\,L$ (the entrywise application of the ring homomorphism $E \to \mathrm{InfiniteAdeleRing}\,L$) the intersection over the infinite places $w$ of $L$ of the preimages, under evaluation $\mathrm{GL}_2(\mathrm{InfiniteAdeleRing}\,L) \to \mathrm{GL}_2(L_w)$ at $w$, of the subgroup of matrices $k$ with $\|\det k\| = 1$ whose transpose-row action preserves $\|x\|^2 + \|y\|^2$ on $L_w^2$. Then there is a constant $c \in (0, \infty)$, $c \ne 0$ and $c \ne \infty$, such that for every Borel measurable $\varphi : \mathrm{GL}_2(E) \to [0,\infty]$,
--   $$\int \varphi \, d\nu = c \int_{E^\times \times E^\times} \int_E \int_{\mathbf{K}} \varphi\!\left(\mathrm{diag}(a_1,a_2)\begin{pmatrix}1&x\\0&1\end{pmatrix} k\right) d\kappa(k)\, d\mathrm{lam}(x)\, d(\rho \times \rho)(a_1,a_2),$$
--   where $\mathrm{diag}(a_1,a_2)$ is `diagUnits2` and the unipotent factor is [`AutomorphicForm.unipotentGL2`](def/AutomorphicForm_ConstantTerm.html#L17) $x$.
--
--   This is the Iwasawa decomposition integration formula $G = ANK$ at the archimedean places, stated for the base-changed group $\mathrm{GL}_2(L \otimes_K K_\infty)$ rather than for $\mathrm{GL}_2(L_\infty)$ directly; the constant $c$ absorbs the normalisations of the four Haar measures. It is obtained from the corresponding formula over a single number field together with the compactness and $BK$-decomposition statement for the intersection of row-isometry subgroups, and it feeds the archimedean estimates for twisted orbital integrals used in the Rankin–Selberg part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions ENNReal Pointwise
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_lintegral_tensor_infiniteAdeleRing_eq_mul_lintegral_diagUnits2_unipotentGL2_archIdentGL_rowIsometry
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(((⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap (archComponent L w) :
          Subgroup (GL (Fin 2) (InfiniteAdeleRing L))).comap (AutomorphicForm.archIdentGL K L) :
        Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ∀ φ : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℝ≥0∞,
        Measurable[AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)] φ →
        @lintegral _ (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν φ =
          c * ∫⁻ a : (L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ, ∫⁻ x : (L ⊗[K] InfiniteAdeleRing K), @lintegral _ (borel _) κ (fun k =>
                φ (diagUnits2 a.1 a.2 * AutomorphicForm.unipotentGL2 x *
                  (k : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) ∂lam ∂(ρ.prod ρ) := by sorry
