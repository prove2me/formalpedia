-- Prove2me | Theorems.Thm_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal
-- name    : AutomorphicForm.exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/e3d3bf23-d177-580b-b01d-04a90dfc34c4
-- title:
--   Coordinate split at a real place for twisted resolvents
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma\in\mathrm{Gal}(L/K)$ be such that every element of $\mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$, and assume $[L:K]$ is prime. Fix a Borel measurable structure on $E:=L\otimes_K\mathbb{A}_{K,\infty}$ (where $\mathbb{A}_{K,\infty}$ is the infinite adele ring of $K$) and an additive Haar measure $\lambda$ on $E$, and let $w'$ be a real infinite place of $L$. Write $\iota$ for the ring homomorphism [`AutomorphicForm.archIdent`](def/AutomorphicForm_TwistedOrbital.html#L420) $E\to\mathbb{A}_{L,\infty}$ obtained by commuting the tensor factors and then applying the base-change isomorphism $\mathbb{A}_{K,\infty}\otimes_K L\cong\mathbb{A}_{L,\infty}$ attached to the genuine infinite place data, and $\rho$ for the ring isomorphism `NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace` from $\mathbb{A}_{L,\infty}$ to the mixed space of $L$. The assertion is that there exist $d\in\mathbb{N}$, an $\mathbb{R}$-linear homeomorphism $e$ from the mixed space of $L$ onto $\mathbb{R}\times\mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ d)$, and a nonzero $\kappa\in\mathbb{R}_{\ge0}$ such that the pushforward of $\lambda$ along $y\mapsto e(\rho(\iota y))$ equals $\kappa$ times the product of Lebesgue measure on $\mathbb{R}$ with Lebesgue measure on $\mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ d)$, and moreover there exists a $C^\infty$ map $\Lambda$ from the mixed space of $L$ to the space of continuous $\mathbb{R}$-linear forms on $\mathrm{EuclideanSpace}\ \mathbb{R}\ (\mathrm{Fin}\ d)$ with the following property: for every $r\in E$, every unit $c$ of $\mathbb{A}_{K,\infty}$ with $c=1-\mathrm{N}_{L\otimes_K\mathbb{A}_{K,\infty}/\mathbb{A}_{K,\infty}}(r)$, and every $\mathbb{A}_{K,\infty}$-linear endomorphism $M$ of $E$ satisfying both twisted resolvent identities $\sigma_*(My)-r\,My=c\,y$ and $M(\sigma_* y-r\,y)=c\,y$ for all $y$ — where $\sigma_*$ is the ring homomorphism $\sigma\otimes\mathrm{id}$ on $E$ — one has, for all $y\in E$, $$\bigl\|(\iota(My))_{w'}\bigr\| = \bigl|\,(e(\rho(\iota y)))_1 + \Lambda\bigl(\rho(\iota r)\bigr)\bigl((e(\rho(\iota y)))_2\bigr)\bigr|,$$ the left-hand side being the norm in the completion of $L$ at $w'$ of the $w'$-component of $\iota(My)$.
--
--   This is the archimedean coordinate computation for the cyclic twisted resolvent at a real place: in suitable global real coordinates on the mixed space of $L$, normalised so that the Haar measure becomes a multiple of Lebesgue measure on $\mathbb{R}\times\mathbb{R}^d$, the $w'$-component of $My$ is the absolute value of one distinguished coordinate of $y$ plus a linear form in the remaining coordinates whose coefficients depend smoothly on $r$. It is used in the subsequent estimate for integrals of $\log$ of the norm of the resolvent against smooth compactly supported kernels in the base-change argument for $\mathrm{GL}(2)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal.lean

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

theorem AutomorphicForm.exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w' : NumberField.InfinitePlace L) (hw' : w'.IsReal) :
    ∃ (d : ℕ) (e : NumberField.mixedEmbedding.mixedSpace L ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin d))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))) lam =
        κ • ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) ∧
      ∃ Λ : NumberField.mixedEmbedding.mixedSpace L → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), ContDiff ℝ (⊤ : ℕ∞) Λ ∧
        ∀ (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ),
          (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r →
        ∀ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
          (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) →
          (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) →
        ∀ y : L ⊗[K] InfiniteAdeleRing K,
          ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ =
            |(e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))).1 + Λ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (r))) (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))).2| := by sorry
