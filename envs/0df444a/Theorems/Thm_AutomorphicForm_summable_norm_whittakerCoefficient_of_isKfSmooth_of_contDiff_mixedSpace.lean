-- Prove2me | Theorems.Thm_AutomorphicForm_summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace
-- name    : AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/78a126a2-7144-54d5-bc72-a64ed3d70663
-- title:
--   Absolute summability of Whittaker coefficients on GL₂
-- statement:
--   Let $K$ be a number field, and write $G = \mathrm{GL}_2(\mathbb{A}_K)$ for the adelic general linear group `AdelicGL2 (𝓞 K) K`. Fix a subset $D \subseteq G$, an assignment $U$ of a subgroup of $G$ to each ideal of $\mathcal{O}_K$, an assignment $\mathrm{gen}$ of an element of $G$ to each finite place, and an additive character $\psi : \mathbb{A}_K \to \mathbb{C}^{\times}$ which is global in the sense that it is trivial on the principal adeles $\mathrm{algebraMap}\,K \to \mathbb{A}_K$, continuous, and not identically $1$. Let $\varphi : G \to \mathbb{C}$ satisfy: (i) $\varphi(n(\beta) g) = \varphi(g)$ for all $\beta \in K$ and $g \in G$, where $n(x) = \begin{pmatrix} 1 & x \\ 0 & 1\end{pmatrix}$; (ii) `IsKfSmooth`, that is, the stabiliser of $\varphi$ under right translation by the subgroup of $G$ of elements with trivial archimedean component (the kernel of `glArch`) is open in that subgroup; (iii) for every $g \in G$ the function $z \mapsto \varphi(n((\iota^{-1} z, 0))\, g)$ on the mixed space $\prod_{v \text{ real}} \mathbb{R} \times \prod_{v \text{ complex}} \mathbb{C}$, where $\iota$ is the ring equivalence from the infinite adeles and the finite component is $0$, is $C^{[K:\mathbb{Q}]+1}$ over $\mathbb{R}$. Then for every $g \in G$ the family
--   $$\alpha \mapsto \Bigl\| \int_{\mathbb{A}_K} \varphi(n(x) g)\, \psi(-\alpha x)\, d\nu(x) \Bigr\|, \qquad \alpha \in K,$$
--   is summable, where $\nu$ is the additive Haar measure on $\mathbb{A}_K$ conditioned on the box `adelicBox K` (infinite part in the preimage of the fundamental domain of the lattice basis of $\mathcal{O}_K$, finite part integral at every height-one prime); this is the Whittaker coefficient `whittakerCoefficient` attached to the carrier data `productionPinsOf K D U gen (adelicBox K)`.
--
--   This is the absolute convergence of the Whittaker–Fourier expansion of a $K_f$-smooth, archimedean-differentiable function on $\mathrm{GL}_2(\mathbb{A}_K)$ that is left invariant under the rational unipotents. It supplies the majorant needed to interchange the sum over $\alpha \in K$ with integration, and is used in the unfolding of Rankin–Selberg integrals and in the realisation of cusp constituents by sums of translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace.lean

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

theorem AutomorphicForm.summable_norm_whittakerCoefficient_of_isKfSmooth_of_contDiff_mixedSpace
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K)) (U : Ideal (𝓞 K) → Subgroup (AdelicGL2 (𝓞 K) K))
    (gen : HeightOneSpectrum (𝓞 K) → AdelicGL2 (𝓞 K) K)
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hleft : ∀ (β : K) (g : AdelicGL2 (𝓞 K) K),
      φ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * g) = φ g)
    (hsm : IsKfSmooth K φ)
    (harch : ∀ g : AdelicGL2 (𝓞 K) K, ContDiff ℝ (Module.finrank ℚ K + 1)
      (fun z : mixedEmbedding.mixedSpace K =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 K) K) ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z, 0) * g))) :
    ∀ g : AdelicGL2 (𝓞 K) K,
      Summable (fun α : K => ‖whittakerCoefficient K (productionPinsOf K D U gen (adelicBox K)) ψ φ α g‖) := by sorry
