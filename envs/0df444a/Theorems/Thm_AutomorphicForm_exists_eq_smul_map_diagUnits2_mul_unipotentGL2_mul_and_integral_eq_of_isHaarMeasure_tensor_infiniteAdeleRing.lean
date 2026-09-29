-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
-- name    : AutomorphicForm.exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/6645d8b9-704d-50a1-bed3-75911292bc0c
-- title:
--   Iwasawa factorisation of Haar measure on GL₂(L⊗_K K_∞)
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite, and write $E = L \otimes_K \mathbb{A}_{K,\infty}$ for the tensor product of $L$ with the infinite adele ring of $K$. Let $\nu$ be a Haar measure on $\mathrm{GL}_2(E)$ for the Borel $\sigma$-algebra of the topology on $\mathrm{GL}_2(E)$; let $E$ and $E^\times$ carry Borel $\sigma$-algebras, let $\lambda$ be an additive Haar measure on $E$, let $\rho$ be a Haar measure on $E^\times$, and let $\kappa$ be a Haar measure, for the Borel $\sigma$-algebra, on the subgroup $\mathcal{K}$ of $\mathrm{GL}_2(E)$ cut out as the intersection, over the infinite places $w$ of $L$, of the preimages under $\mathrm{GL}_2(E) \to \mathrm{GL}_2(\mathbb{A}_{L,\infty}) \to \mathrm{GL}_2(L_w)$ (the base-change identification [`AutomorphicForm.archIdentGL`](def/AutomorphicForm_TwistedOrbital.html#L424) followed by the $w$-component map) of the group of $k \in \mathrm{GL}_2(L_w)$ with $\lVert \det k\rVert = 1$ satisfying $\lVert x k_{00} + y k_{10}\rVert^2 + \lVert x k_{01} + y k_{11}\rVert^2 = \lVert x\rVert^2 + \lVert y\rVert^2$ for all $x, y \in L_w$. Then there is a constant $c \in (0,\infty)$, finite and non-zero, such that $\nu$ equals $c$ times the pushforward of $(\rho \times \rho) \times (\lambda \times \kappa)$ along the map $((x,y),(u,k)) \mapsto \mathrm{diag}(x,y) \cdot \begin{pmatrix}1 & u\\ 0 & 1\end{pmatrix} \cdot k$, and such that for every measurable $f : \mathrm{GL}_2(E) \to \mathbb{C}$ one has $\int f \, d\nu = c \int f\bigl(\mathrm{diag}(x,y)\,n(u)\,k\bigr) \, d\bigl((\rho \times \rho) \times (\lambda \times \kappa)\bigr)$, with no integrability hypothesis on $f$.
--
--   This is the Iwasawa decomposition of Haar measure for $\mathrm{GL}_2$ over the archimedean base change $L \otimes_K \mathbb{A}_{K,\infty}$, in the torus–unipotent–maximal-compact order and with no modular factor, together with its Bochner-integral form for complex-valued measurable functions. It feeds the computation of archimedean twisted orbital integrals at diagonal elements used in the twisted trace formula input to the Langlands–Tunnell step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing.lean

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

open scoped ENNReal

theorem AutomorphicForm.exists_eq_smul_map_diagUnits2_mul_unipotentGL2_mul_and_integral_eq_of_isHaarMeasure_tensor_infiniteAdeleRing
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (ν : @Measure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)))
    (hν : @Measure.IsHaarMeasure (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) _ _
      (AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)) ν)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)ˣ] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)ˣ]
    (ρ : Measure (L ⊗[K] InfiniteAdeleRing K)ˣ) [ρ.IsHaarMeasure]
    (κ : @Measure (↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) (borel _))
    (hκ : @Measure.IsHaarMeasure _ _ _ (borel _) κ) :
    letI : MeasurableSpace (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :=
      AutomorphicForm.glBorelOf (L ⊗[K] InfiniteAdeleRing K)
    letI : MeasurableSpace ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) := borel _
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ν = c • Measure.map
        (fun p : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
            ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))) =>
          diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 *
            (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))
        ((ρ.prod ρ).prod (lam.prod κ)) ∧
      ∀ f : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K) → ℂ, Measurable f →
        ∫ x, f x ∂ν =
          (c.toReal : ℂ) *
            ∫ p : ((L ⊗[K] InfiniteAdeleRing K)ˣ × (L ⊗[K] InfiniteAdeleRing K)ˣ) ×
                ((L ⊗[K] InfiniteAdeleRing K) × ↥(⨅ w : InfinitePlace L,
        (AutomorphicForm.WindowedSiegel.rowIsometrySubgroup w.Completion).comap
          ((archComponent L w).comp (AutomorphicForm.archIdentGL K L)) :
          Subgroup (GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)))),
              f (diagUnits2 p.1.1 p.1.2 * AutomorphicForm.unipotentGL2 p.2.1 *
                (p.2.2 : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K))) ∂((ρ.prod ρ).prod (lam.prod κ)) := by sorry
