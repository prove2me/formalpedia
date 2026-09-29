-- Prove2me | Theorems.Thm_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
-- name    : AutomorphicForm.eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/a2427bd6-4ad9-5099-ba90-a34b23684c9a
-- title:
--   Cuspidal functions trivial under SL₂(ℝ) at a real place vanish
-- statement:
--   Let $F$ be a number field. Fix a subset $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ (where $\mathrm{GL}_2(\mathbb{A}_F)$ denotes `AdelicGL2 (𝓞 F) F`, the general linear group of degree $2$ over the adele ring of $\mathcal{O}_F$ in $F$), a family $U$ of subgroups of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the ideals of $\mathcal{O}_F$, and a family $\mathrm{gen}$ of elements of $\mathrm{GL}_2(\mathbb{A}_F)$ indexed by the height-one primes of $\mathcal{O}_F$; these three enter only through `productionPinsOf F D U gen (adelicBox F)`, and only through its $\sigma$-algebra and measure on the adele ring, namely the Borel $\sigma$-algebra and the additive Haar measure conditioned to the adelic box $\{x : x_\infty \text{ lies in the preimage of the fundamental domain of the lattice basis of the mixed space, and } x_v \text{ is integral at every height-one prime}\}$, neither of which depends on $D$, $U$, $\mathrm{gen}$. Let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be continuous and invariant under left translation by the image of $\mathrm{GL}_2(F)$ under `globalPoints`, i.e. $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathrm{GL}_2(F)$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$. Assume $\varphi$ is cuspidal for the family $x \mapsto \mathrm{unipotentGL2}(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$ in the sense of `IsCuspidalFn`: for every $g$, the integral over the adele ring of `constantTermIntegrand unipotentGL2 φ g` with respect to the above conditioned measure vanishes. Finally let $w$ be a real infinite place of $F$ and assume $\varphi(g \cdot \mathrm{archRealGLAt}\,hw\,(h)) = \varphi(g)$ for all $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and all $h \in \mathrm{GL}_2(\mathbb{R})$ with $\det h = 1$, where `archRealGLAt` transports $h$ entrywise through the inverse of the isomorphism $F_w \cong \mathbb{R}$ and includes the result into $\mathrm{GL}_2(\mathbb{A}_F)$ at $w$. Then $\varphi = 0$.
--
--   This is the statement that a cuspidal automorphic function on $\mathrm{GL}_2(\mathbb{A}_F)$ on which $\mathrm{SL}_2(F_w)$ acts trivially at a real place $w$ must vanish, so that the trivial representation cannot occur as an archimedean component of the cuspidal spectrum. It is used in [`AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre`](thm.html#AutomorphicForm.one_le_of_archOccursInClassOf_isArchLoweringAnnihilatedAt_of_coversModCentre) to force a lower bound on archimedean weights, and is proved from the Fourier expansion of $\varphi$ along $N(F)\backslash N(\mathbb{A}_F)$ via [`AutomorphicForm.hasSum_whittakerCoefficient`](thm.html#AutomorphicForm.hasSum_whittakerCoefficient) together with the transformation rule [`AutomorphicForm.whittakerCoefficient_unipotentGL2_mul`](thm.html#AutomorphicForm.whittakerCoefficient_unipotentGL2_mul) and the standard global additive character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain

theorem AutomorphicForm.eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      φ (g * archRealGLAt hw h) = φ g) :
    φ = 0 := by sorry
