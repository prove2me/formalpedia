-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/99ab2d79-8b7d-57d4-ba2e-612b675568f4
-- title:
--   A level-average idempotent on the cuspidal carrier
-- statement:
--   Let $F$ be a number field, $\alpha,\beta$ real numbers and $\Phi_0$ a subset of $\mathrm{GL}_2$ of the adeles of $F$ which is a slab fundamental domain in the sense that $0<\alpha<\beta$, $\Phi_0$ lies in the determinant-norm slab $(\alpha,\beta)$ and $\Phi_0$ is a fundamental domain for the image of the global points acting on the adelic $\mathrm{GL}_2$ Haar measure restricted to that slab; let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full group of idele units to $\mathbb C^\times$ of modulus $\sigma$, i.e. $\|\xi(z)\|$ equals the $\sigma$-th power of the idele norm of $z$. Let $U$ be a subgroup with compact underlying set and $O$ an open subgroup such that $U=O\cap\ker(\mathrm{glArch})$, the intersection of $O$ with the finite-adelic subgroup. Write $\mathcal H=$ `cuspSubcarrier F hΦ₀ σ ξ`, the closure inside the carrier of the image of the cuspidal members, the continuous $\varphi$ satisfying the smooth cuspidal automorphy condition at the pins of $\Phi_0$ with central character $\xi$, and $[\varphi]$ for the class of such a $\varphi$ in $\mathcal H$. Then there is a continuous $\mathbb C$-linear operator $A$ on $\mathcal H$ such that: $A\circ A=A$; every submodule $M\subseteq\mathcal H$ satisfying `IsClosedCuspSubrep` (closed, and stable under the operators lifting right translations by finite adelic elements, right translations by determinant-one row isometries at the infinite places, and right convolution by factorizable archimedean bi-finite test functions) satisfies $A(M)\subseteq M$; $A[\varphi]=[\varphi]$ for every cuspidal member $\varphi$ with $\varphi(gk)=\varphi(g)$ for all $g$ and all $k\in U$; for every cuspidal member $\varphi$ there is a cuspidal member $\varphi'$ with $\varphi'(gk)=\varphi'(g)$ for $k\in U$, belonging to `archCutSubmodule F tys` for every archimedean type family `tys` to which $\varphi$ belongs, belonging to every $\mathbb C$-submodule $V$ of functions which contains $\varphi$ and is stable under right translation by finite adelic elements, and with $A[\varphi]=[\varphi']$; $A$ commutes with every continuous operator $T$ on $\mathcal H$ that commutes with all operators lifting right translation by elements of $U$; and $A$ commutes with every operator lifting right translation by $\mathrm{rowIsometryInclAt₀}\,(w,k)$ for $w$ an infinite place of $F$ and $k$ a determinant-one row isometry over the completion at $w$.
--
--   This is the level projector $e_U=\int_U S_u\,du$ attached to a compact open level subgroup of the finite adelic points, realised on the cuspidal carrier: a bounded idempotent fixing exactly the right-$U$-invariant classes, stable on closed cuspidal sub-representations, and commuting with the archimedean row-isometry action. It is the finite-adelic half of the level-and-type cut, and is used by [`AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact`](thm.html#AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_levelAverage_of_isCompact.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_idempotent_levelAverage_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F) :
    ∃ A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      A.comp A = A ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M → M.map (A : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) →
        A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧
          (∀ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys → φ' ∈ archCutSubmodule F tys) ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ ψ ∈ V, rightTranslate F g ψ ∈ V) → φ ∈ V → φ' ∈ V) ∧
          A (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ u ∈ U, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F u) S → S.comp Tc = Tc.comp S) →
        A.comp Tc = Tc.comp A) ∧
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
        IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → A.comp S = S.comp A) := by sorry
