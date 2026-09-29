-- Prove2me | Theorems.Thm_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
-- name    : AutomorphicForm.isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/c62d52e3-ad54-5050-8af0-09c9eb88f753
-- title:
--   Averaging over the maximal compact preserves cuspidality
-- statement:
--   Let $K$ be a number field and let $\nu$ be a measure on the adele ring $\mathbb{A}_K$ for the Borel $\sigma$-algebra `adeleBorel` with finite total mass, $\nu(\mathbb{A}_K)\neq\infty$, and suppose there is a compact set $B\subseteq\mathbb{A}_K$ with $\nu(B^{c})=0$. Let $\mathcal{K}=$ `maximalCompactAt K ∅` be the subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$ consisting of those $k$ whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place of $K$ is a row isometry, intersected with the kernels of all the finite-place component maps `finComponent v ∘ glFin` (the index set $S=\emptyset$ makes the intersection run over every finite place), equipped with the Haar measure `maximalCompactAtHaar K ∅` $=$ `Measure.haarMeasure ⊤`. Let $\kappa\colon\mathcal{K}\to\mathbb{R}$ and $f\colon \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, and assume $f$ satisfies `IsCuspidalFn` for $\nu$ and the unipotent family $q\mapsto n(q)=\begin{pmatrix}1&q\\0&1\end{pmatrix}$, i.e. for every $g$ the $\nu$-integral over $q\in\mathbb{A}_K$ of `constantTermIntegrand` formed from this family, $f$ and $g$ vanishes. The conclusion is that the averaged function $x\mapsto\int_{\mathcal{K}}\kappa(k)\,f(xk)\,d k$ satisfies the same vanishing condition: it is again `IsCuspidalFn` for $\nu$ and the family $q\mapsto n(q)$.
--
--   This is the statement that the space of functions with vanishing adelic constant terms is stable under right convolution by a continuous kernel on the maximal compact subgroup at the empty level, the operation used to produce $K$-finite vectors from a cusp form. It is used by [`AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule`](thm.html#AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule), where such averages are placed in an isotypic cuspidal submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K)) (hν : ν Set.univ ≠ ⊤)
    (B : Set (AdeleRing (𝓞 K) K)) (hB : IsCompact B) (hνB : ν Bᶜ = 0)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f)
    (hfc : @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) f) :
    @IsCuspidalFn (AdeleRing (𝓞 K) K) (adeleBorel (𝓞 K) K) (AdelicGL2 (𝓞 K) K) _ ν
      (fun q => unipotentGL2 q) (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) := by sorry
