-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
-- name    : AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/bd9fc16e-3a53-5a38-83d8-0526278ed685
-- title:
--   Closure of a cuspidal subrepresentation's class image is closed subrepresentation
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real numbers and let $\Phi_0$ be a subset of $\mathrm{GL}_2$ of the adeles of $F$ which is a slab fundamental domain: $0<\alpha<\beta$, $\Phi_0$ lies in the determinant-norm slab between $\alpha$ and $\beta$, and $\Phi_0$ is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ under `globalPoints` on the adelic Haar measure of $\mathrm{GL}_2$ restricted to that slab. Let $\sigma$ be a real number, let $\xi$ be a homomorphism from the full subgroup of ideles units to $\mathbb{C}^\times$, and let $W$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsCuspSubrep` at the pins `fdPins F Φ₀` (the pins with domain $\Phi_0$, central subgroup $\top$, level subgroups `levelOne` intersected with the finite adelic subgroup, Hecke generators `heckeGen`, Borel structures, adelic Haar measure, and the additive Haar measure conditioned on `adelicBox`) and the character $\xi$: that is, $W$ is contained in the $K$-finite cusp submodule for these data, and is stable under right translation by elements of the finite adelic subgroup, under right translation by the archimedean row isometries `rowIsometryInclAt₀ F w k` at each infinite place $w$, and under right convolution with every factorizable test function that is archimedean bi-finite for some archimedean type family. Then the topological closure of the image, under `toCuspSubcarrier F hΦ₀ σ ξ`, of the preimage of $W$ in the submodule `cuspMemberSubmodule F Φ₀ ξ` (continuous smooth cuspidal automorphic functions for these pins and $\xi$) satisfies `IsClosedCuspSubrep`: it is a closed submodule of the cusp subcarrier, and it is mapped into itself by every continuous linear endomorphism $S$ of the cusp subcarrier which is a cusp lift (`IsCuspLift`) of right translation by a finite adelic element, of right translation by an archimedean row isometry, or of right convolution with a factorizable archimedean bi-finite test function.
--
--   This transports a cuspidal subrepresentation of the space of automorphic functions into the Hilbert-space setting of the cuspidal subcarrier, producing a closed invariant subspace; it is the step that makes representation-theoretic arguments on the carrier available. It is used in the transfer of irreducibility and minimality to the carrier, in the dichotomy for intersections with closed irreducible subrepresentations, and in the construction of orthonormal isotypic cusp submodules at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hW : IsCuspSubrep F (fdPins F Φ₀) ξ W) :
    IsClosedCuspSubrep F hΦ₀ σ ξ
      (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
        (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W)).topologicalClosure := by sorry
