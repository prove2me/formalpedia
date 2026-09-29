-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector
-- name    : AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/3d2ad44f-7fcd-50b0-870e-f6d5bb88cb88
-- title:
--   An idempotent archimedean type projector on the cuspidal carrier
-- statement:
--   Let $F$ be a number field, $\alpha,\beta$ reals and $\Phi_0$ a subset of $\mathrm{GL}_2$ of the adeles which is a slab fundamental domain: $0<\alpha<\beta$, $\Phi_0$ lies in the determinant-norm slab between $\alpha$ and $\beta$, and $\Phi_0$ is a fundamental domain for the image of the global points acting on that slab with the restricted adelic Haar measure. Let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full group of ideles to $\mathbb C^\times$ of modulus $\sigma$, i.e. $\|\xi(z)\| = \mathrm{ideleNorm}(z)^{\sigma}$ for all $z$, and let `tys` be an archimedean type family, assigning to each infinite place $w$ a number $\mathrm{card}(w)$ of representation data $\mathrm{rep}\,w\,i$ at $w$. Then there is a continuous $\mathbb C$-linear operator $E$ on the cuspidal subcarrier $\mathcal H =$ `cuspSubcarrier F hΦ₀ σ ξ` (the closure, inside the carrier attached to $\Phi_0$ and $\sigma$, of the image of the space `cuspMemberSubmodule F Φ₀ ξ` of continuous smooth cuspidal automorphic functions with central behaviour $\xi$) with the following properties. First, $E\circ E=E$. Second, every submodule $M\subseteq\mathcal H$ satisfying `IsClosedCuspSubrep` — $M$ closed and mapped into itself by every lift to $\mathcal H$ of right translation by a finite-adelic element, of right translation by an archimedean determinant-one row isometry, and of right convolution by a factorizable test function which is archimedean bi-finite for some type family — satisfies $M.\mathrm{map}\,E\le M$. Third, $E$ fixes the class of any $\varphi\in$ `cuspMemberSubmodule` lying in $\mathrm{archCutSubmodule}(\mathrm{tys}) = \bigcap_w \sum_{i<\mathrm{card}(w)} \mathrm{archTypeSubmoduleAt}(w,\mathrm{rep}\,w\,i)$. Fourth, for any $\varphi\in$ `cuspMemberSubmodule` lying in the arch-cut submodule of some type family there is $\varphi'\in$ `cuspMemberSubmodule` with $\varphi'$ in the arch-cut submodule of `tys`, such that $\varphi'$ is right invariant under every subgroup $U$ of the finite-adelic subgroup (the kernel of the archimedean projection) under which $\varphi$ is right invariant, $\varphi'$ lies in every $\mathbb C$-submodule of functions containing $\varphi$ and stable under right translation by the inclusions of determinant-one row isometries at the infinite places, and $E$ sends the class of $\varphi$ to the class of $\varphi'$. Fifth, $E$ commutes with every continuous operator on $\mathcal H$ that commutes with all lifts of right translations by determinant-one archimedean row isometries; and sixth, $E$ commutes with every lift of right translation by an element of the finite-adelic subgroup, where a lift of an operation $\mathrm{op}$ on functions means an operator sending the class of $\varphi$ to the class of $\mathrm{op}\,\varphi$ whenever the latter again lies in `cuspMemberSubmodule`.
--
--   This is the archimedean half of the projector cutting out a fixed finite set of $K_\infty$-types in the cuspidal spectrum: a bounded idempotent built from the isotypic weight function of the listed types, compatible with closed cuspidal sub-representations, with finite-adelic level structures and with the finite-adelic Hecke action. It is used in the construction of the combined level-and-type cut projector, [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_archTypeProjector.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_idempotent_archTypeProjector
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (tys : ArchTypeFamily F) :
    ∃ E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      E.comp E = E ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M → M.map (E : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        φ ∈ archCutSubmodule F tys →
        E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∃ tys' : ArchTypeFamily F, φ ∈ archCutSubmodule F tys') →
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          φ' ∈ archCutSubmodule F tys ∧
          (∀ U : Subgroup (AdelicGL2 (𝓞 F) F), U ≤ finiteAdelicGL2Subgroup F →
            (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) → ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ ψ ∈ V,
              rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V) → φ ∈ V → φ' ∈ V) ∧
          E (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → S.comp Tc = Tc.comp S) →
        E.comp Tc = Tc.comp E) ∧
      (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S → E.comp S = S.comp E) := by sorry
