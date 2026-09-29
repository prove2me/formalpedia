-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/7a2283fc-66ff-5b1d-912f-5d7dabb58805
-- title:
--   Existence of a level-and-type cut projector on the cuspidal carrier
-- statement:
--   Let $F$ be a number field, let $\alpha,\beta$ be real and let $\Phi_0\subseteq \mathrm{GL}_2(\mathbb A_F)$ satisfy `IsSlabFundamentalDomain`, i.e. $0<\alpha<\beta$, $\Phi_0$ lies in the slab `detNormSlab F α β` and $\Phi_0$ is a fundamental domain for the range of the global points acting on the adelic Haar measure restricted to that slab. Let $\sigma\in\mathbb R$ and let $\xi$ be a homomorphism from the full unit group of the adele ring to $\mathbb C^\times$ with $\lVert\xi(z)\rVert$ equal to the $\sigma$-th power of the idele norm of $z$ for all $z$. Let $U$ be a compact subgroup of $\mathrm{GL}_2(\mathbb A_F)$ of the form $U=O\cap\ker(\mathrm{glArch})$ for an open subgroup $O$, where the second factor is the finite-adelic subgroup, and let `tys` assign to each infinite place $w$ a natural number and that many archimedean types at $w$. Then there is a continuous $\mathbb C$-linear operator $P$ on the cuspidal subcarrier $\mathcal H$ — the topological closure, inside the carrier `Carrier F Φ₀ σ`, of the image of those continuous smooth cuspidal automorphic functions with central behaviour $\xi$ relative to the pins of $\Phi_0$ — such that: (i) $P\circ P=P$; (ii) every submodule $M\subseteq\mathcal H$ satisfying `IsClosedCuspSubrep` (closed, and stable under all cusp lifts of right translation by finite-adelic elements, of right translation by archimedean row isometries, and of right convolution by factorizable archimedean-bifinite test functions) has $P(M)\subseteq M$; (iii) if $\varphi$ is such a cuspidal member with $\varphi(gk)=\varphi(g)$ for all $g$ and all $k\in U$ and $\varphi$ lies in $\bigcap_w\sum_i$ `archTypeSubmoduleAt F w (tys.rep w i)`, then $P$ fixes the class of $\varphi$; (iv) if $\varphi$ is a cuspidal member lying in the archimedean cut submodule of some type family, then there is a cuspidal member $\varphi'$ which is right $U$-invariant, lies in the archimedean cut submodule of `tys`, belongs to every submodule $V$ of complex-valued functions containing $\varphi$ that is stable under right translation by finite-adelic elements and by the elements `rowIsometryInclAt₀ F w k`, and satisfies $P[\varphi]=[\varphi']$; and (v) $P$ commutes with every continuous operator $T_c$ on $\mathcal H$ that commutes with all cusp lifts of right translation by elements of $U$ and with all cusp lifts of right translation by the archimedean row isometries.
--
--   This is the construction of the combined level-averaging and archimedean isotypic cut projector on the space of cuspidal classes: a bounded idempotent which fixes the classes of $U$-invariant forms of the prescribed archimedean types, preserves every closed cuspidal sub-representation, and lies in the commutant of the operators commuting with the lifted translations. It is used in the isolation of irreducible cuspidal constituents and in the production of orthonormal families in isotypic cuspidal subspaces at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact.lean

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

theorem AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F) :
    ∃ P : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      P.comp P = P ∧
      (∀ M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ), IsClosedCuspSubrep F hΦ₀ σ ξ M →
        M.map (P : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g) → φ ∈ archCutSubmodule F tys →
        P (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∧
      (∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        (∃ tys' : ArchTypeFamily F, φ ∈ archCutSubmodule F tys') →
        ∃ (φ' : AdelicGL2 (𝓞 F) F → ℂ) (hφ' : φ' ∈ cuspMemberSubmodule F Φ₀ ξ),
          (∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ' (g * k) = φ' g) ∧ φ' ∈ archCutSubmodule F tys ∧
          (∀ V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
            (∀ g ∈ finiteAdelicGL2Subgroup F, ∀ ψ ∈ V, rightTranslate F g ψ ∈ V) →
            (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ ψ ∈ V,
              rightTranslate F (rowIsometryInclAt₀ F w k) ψ ∈ V) →
            φ ∈ V → φ' ∈ V) ∧
          P (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨φ', hφ'⟩) ∧
      (∀ Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
        (∀ u ∈ U, ∀ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F u) S → S.comp Tc = Tc.comp S) →
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
          (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
          IsCuspLift F hΦ₀ σ ξ (rightTranslate F (rowIsometryInclAt₀ F w k)) S → S.comp Tc = Tc.comp S) →
        P.comp Tc = Tc.comp P) := by sorry
