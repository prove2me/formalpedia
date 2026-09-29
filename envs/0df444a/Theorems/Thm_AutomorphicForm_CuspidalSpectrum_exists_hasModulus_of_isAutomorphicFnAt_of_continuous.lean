-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous
-- name    : AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/9db16a64-7d1d-58d6-8434-138b3a8ca1c0
-- title:
--   A continuous nonzero automorphic function pins its central modulus
-- statement:
--   Let $F$ be a number field, let $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be an arbitrary subset, let $\xi$ be a group homomorphism from the full subgroup $\top$ of $\mathbb{A}_F^\times$ to $\mathbb{C}^\times$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a function. Assume $\varphi$ satisfies the predicate `IsAutomorphicFnAt` with central character $\xi$ for the package of data `productionPinsOf` built from: the Borel $\sigma$-algebra on $\mathrm{GL}_2(\mathbb{A}_F)$ together with its Haar measure `adelicGLHaar`, the carrier set $D$, the central subgroup taken to be all of $\mathbb{A}_F^\times$, the level family sending an ideal $N$ of $\mathcal{O}_F$ to the intersection of `levelOne` at $N$ with `finiteAdelicGL2Subgroup` (the kernel of the archimedean projection `glArch`), the Hecke elements $v \mapsto$ `heckeGen` at each finite place, and, on the adeles, the Borel $\sigma$-algebra with additive Haar measure conditioned on the box `adelicBox` (a fundamental domain for the Minkowski lattice at the infinite places times the integral finite adeles); this predicate is the $L^s$-with-character membership condition `LsXiMember` for those data. Assume further that $\varphi$ is continuous and not the zero function. Then there exists a real number $\sigma$ such that `HasModulus F ξ σ` holds, i.e. $\lVert \xi(z) \rVert = \lVert z \rVert_{\mathbb{A}}^{\sigma}$ for every idele $z$, where $\lVert\cdot\rVert_{\mathbb{A}}$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19).
--
--   This is the standard fact that a quasi-character of the idele class group is an unramified twist of a power of the idele norm, in the form needed to read off the exponent $\sigma$ attached to a nonzero continuous automorphic function: the central character of such a function has modulus $\lVert\cdot\rVert_{\mathbb{A}}^{\sigma}$. It is used throughout the cuspidal-spectrum layer, where cusp forms are placed in a weighted $L^2$-space with weight governed by $\sigma$, and is invoked by the constituent and isotypic versions of those statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_hasModulus_of_isAutomorphicFnAt_of_continuous.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_hasModulus_of_isAutomorphicFnAt_of_continuous
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsAutomorphicFnAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ φ)
    (hφc : Continuous φ) (hφ0 : φ ≠ 0) :
    ∃ σ : ℝ, HasModulus F ξ σ := by sorry
