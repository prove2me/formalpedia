-- Prove2me | Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
-- name    : AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/bd3cf765-0aaa-5abf-b943-eb5541d1eac2
-- title:
--   Integrability and summability of adelic GL₂ Whittaker coefficients
-- statement:
--   Let $K$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, let $U$ assign to each ideal of $\mathcal{O}_K$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_K)$, and let $\mathrm{gen}$ assign to each finite place an element of $\mathrm{GL}_2(\mathbb{A}_K)$; these three pieces of data are carried along unused in the conclusion. Let $\psi$ be an additive character of $\mathbb{A}_K$ with values in $\mathbb{C}$ which is trivial on the image of $K$, continuous, and not identically $1$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ satisfy: (i) $\varphi(n(\beta)g) = \varphi(g)$ for all $\beta \in K$ and all $g$, where $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$; (ii) $\varphi$ is a smooth vector for right translation by the kernel of the archimedean projection of $\mathrm{GL}_2(\mathbb{A}_K)$, i.e. the predicate `IsKfSmooth`; (iii) for each $g$ the function $z \mapsto \varphi(n((z,0))g)$ on the mixed space $\prod_{v\mid\infty}K_v$, with $z$ transported to the infinite adeles and zero finite component, is $C^{[K:\mathbb{Q}]+1}$ over $\mathbb{R}$. Let $\nu$ be the additive Haar measure of $\mathbb{A}_K$ (Borel $\sigma$-algebra) conditioned on the adelic box, i.e. on the set of adeles whose infinite component lies in the preimage of the fundamental domain of the lattice basis of $K$ and whose finite component is integral at every place. Then: for every $\alpha \in K$ and every $g$ the function $x \mapsto \varphi(n(x)g)\,\psi(-\alpha x)$ is $\nu$-integrable; and for every $g$ the family of its integrals, the Whittaker coefficients $\alpha \mapsto \int \varphi(n(x)g)\,\psi(-\alpha x)\,d\nu(x)$, is summable over $\alpha \in K$.
--
--   This is the basic convergence input for the Whittaker–Fourier expansion of a function on $\mathrm{GL}_2(\mathbb{A}_K)$ that is left invariant under the rational unipotents, smooth at the finite places and sufficiently differentiable at the archimedean ones: the coefficients exist and form an absolutely summable family indexed by $K$. It is used in the estimates on class sums and in the Rankin–Selberg constructions that rest on term-by-term manipulation of that expansion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace.lean

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicBox

open scoped Classical in

theorem AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ)
    (harch : ∀ g : AdelicGL2 (𝓞 K) K,
      ContDiff ℝ (Module.finrank ℚ K + 1) (fun z : mixedEmbedding.mixedSpace K =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 K) K)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))) :
    (∀ (α : K) (g : AdelicGL2 (𝓞 K) K),
        WhittakerCoefficientIntegrable K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) ∧
      ∀ g : AdelicGL2 (𝓞 K) K,
        Summable (fun α : K =>
          whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g) := by sorry
