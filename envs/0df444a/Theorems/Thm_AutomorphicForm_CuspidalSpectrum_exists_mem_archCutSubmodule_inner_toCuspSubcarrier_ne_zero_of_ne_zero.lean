-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
-- name    : AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/1810c5fe-8cb6-5d73-bf6e-4e2453331a53
-- title:
--   Non-zero cusp-carrier vectors pair with K-finite level forms
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real numbers and let $\Phi_0$ be a subset of $\mathrm{GL}_2$ of the adeles of $F$ satisfying `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, $\Phi_0$ is contained in the determinant-norm slab `detNormSlab F α β`, and $\Phi_0$ is a fundamental domain for the range of `globalPoints`, the image of $\mathrm{GL}_2(F)$ in $\mathrm{GL}_2$ of the adeles, acting on the adelic Haar measure restricted to that slab. Let $\sigma\in\mathbb{R}$ and let $\xi$ be a homomorphism from the full subgroup of the idele units to $\mathbb{C}^\times$ with modulus $\sigma$, meaning $\|\xi(z)\|=\mathrm{ideleNorm}_F(z)^{\sigma}$ for every $z$. Let $v$ be a non-zero element of `cuspSubcarrier F hΦ₀ σ ξ`, the topological closure, inside the carrier space, of the image under `toCarrier` of the cuspidal members, i.e. of those members of the $\xi$-isotypic space at $\Phi_0$ that are continuous and satisfy the vanishing of all constant terms. Then there exist: a family of archimedean types $\mathrm{tys}$, consisting of a cardinality function $w\mapsto \mathrm{card}(w)$ on the infinite places of $F$ together with representations $\mathrm{rep}\,w\colon \mathrm{Fin}(\mathrm{card}\,w)\to$ `ArchRepAt F w`; a subgroup $U$ of $\mathrm{GL}_2$ of the adeles contained in `finiteAdelicGL2Subgroup F` (the kernel of the archimedean projection `glArch`) whose image under the finite-adelic projection `glFin` is open, compact and contained in `finiteIntegralGL2`; and a function $\psi$ on $\mathrm{GL}_2$ of the adeles lying in `cuspMemberSubmodule F Φ₀ ξ`, such that $\psi$ belongs to `archCutSubmodule F tys`, namely the intersection over all infinite places $w$ of the sum of the submodules `archTypeSubmoduleAt F w (tys.rep w i)` for $i<\mathrm{card}\,w$; such that $\psi(gu)=\psi(g)$ for all $g$ and all $u\in U$; and such that the Hermitian pairing of $v$ with the class `toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩` is non-zero.
--
--   This is the separation statement underlying the passage from the abstract cuspidal carrier to concrete cusp forms: the classes of cusp forms which are finite for the archimedean maximal compact (a finite family of types at each infinite place) and invariant under a compact open subgroup of level structure at the finite places span a dense subspace, so no non-zero carrier vector is orthogonal to all of them. It feeds the construction of compact operators on the cuspidal carrier by right convolution with such level and type data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_mem_archCutSubmodule_inner_toCuspSubcarrier_ne_zero_of_ne_zero
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : v ≠ 0) :
    ∃ (tys : AutomorphicForm.ArchTypeFamily F) (U : Subgroup (AdelicGL2 (𝓞 F) F)),
      U ≤ finiteAdelicGL2Subgroup F ∧
      IsOpen ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      IsCompact ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) ∧
      (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) ⊆ (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) ∧
      ∃ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ cuspMemberSubmodule F Φ₀ ξ),
        ψ ∈ archCutSubmodule F tys ∧ (∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, ψ (g * u) = ψ g) ∧
        ⟪v, toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψ⟩⟫_ℂ ≠ 0 := by sorry
