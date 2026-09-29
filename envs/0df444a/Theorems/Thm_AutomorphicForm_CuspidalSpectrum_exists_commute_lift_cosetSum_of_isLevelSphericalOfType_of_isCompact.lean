-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
-- name    : AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/42ab5a5f-8b35-5f32-8265-d0aa09139f3f
-- title:
--   Hecke coset-sum operator on the cuspidal sub-carrier, compact level
-- statement:
--   Let $F$ be a number field. Fix reals $\alpha,\beta$ and a set $\Phi_0 \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ with `IsSlabFundamentalDomain F α β Φ₀`, i.e. $0<\alpha<\beta$, $\Phi_0$ is contained in the determinant-norm slab between $\alpha$ and $\beta$ and is a fundamental domain for the action of the image of $\mathrm{GL}_2(F)$ on that slab for the restricted adelic Haar measure; fix $\sigma \in \mathbb{R}$ and a homomorphism $\xi$ from the full idèle unit group to $\mathbb{C}^\times$ with $\|\xi(z)\| = \|z\|^{\sigma}$ for all $z$. Let $U$ be a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$ with compact underlying set, arising as $U = O \cap \ker(\mathrm{gl}_{\mathrm{arch}})$ for an open subgroup $O$, where $\ker(\mathrm{gl}_{\mathrm{arch}})$ is the finite-adelic subgroup. Let `tys` be a family of archimedean types and let $f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ be a factorizable test function (a product of an archimedean test factor and a finite test factor) which is moreover level-spherical of type `tys` for $U$: $f(g) = f_\infty(g_\infty)\,\mathbf{1}_{\mathrm{gl}_{\mathrm{fin}}(U)}(g_{\mathrm{fin}})$ with $f_\infty$ an archimedean test factor, bi-finite of type `tys`, and invariant under conjugation by the row-isometry subgroups at each infinite place. Let $T_c$ be a continuous $\mathbb{C}$-linear operator on the cuspidal sub-carrier $\mathrm{cuspSubcarrier}$ (the closure, inside the carrier $\mathrm{Carrier}\,F\,\Phi_0\,\sigma$, of the image of the continuous cuspidal members) which implements right convolution by $f$: for every $\varphi$ in the cuspidal member submodule such that $\varphi * f$ again lies in that submodule, $T_c$ sends the class of $\varphi$ to the class of $\varphi * f$. Finally let $g$ be finite-adelic, $n \in \mathbb{N}$ and $\mathrm{reps} : \mathrm{Fin}\,n \to \mathrm{GL}_2(\mathbb{A}_F)$ satisfy: each $\mathrm{reps}\,i$ lies in $UgU$; every element of $UgU$ lies in some $\mathrm{reps}\,i \cdot U$; and $(\mathrm{reps}\,i)^{-1}\mathrm{reps}\,j \in U$ forces $i=j$ — so the $\mathrm{reps}\,i$ are representatives of the distinct cosets $\gamma U$ making up $UgU$. The conclusion asserts the existence of a continuous $\mathbb{C}$-linear operator $S$ on the cuspidal sub-carrier with $S \circ T_c = T_c \circ S$ and such that for every member $\varphi$ of the cuspidal member submodule whose underlying function is invariant under the right regular representation restricted to $U$, the function $x \mapsto \sum_i \varphi(x\,\mathrm{reps}\,i)$ again belongs to the cuspidal member submodule and $S$ carries the class of $\varphi$ to the class of that coset sum.
--
--   This provides the Hecke operator attached to a double coset $UgU$ at an arbitrary compact level of the form $O \cap \mathrm{GL}_2(\mathbb{A}_{F,\mathrm{fin}})$, realised as a bounded operator on the cuspidal sub-carrier and commuting with the smoothing operator given by convolution with a level-spherical test function. It is used in the spectral analysis of the cuspidal sub-representation, in the production of slices inside eigenspaces orthogonal to a prescribed vector and in the dichotomy for images of irreducible cuspidal sub-representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact.lean

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_ArchSpherical

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.CuspidalSpectrum.exists_commute_lift_cosetSum_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hsph : IsLevelSphericalOfType F tys U f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hcomm : ∀ (φ : ↥(cuspMemberSubmodule F Φ₀ ξ)) (hφ' : rightConv F φ f ∈ cuspMemberSubmodule F Φ₀ ξ),
        Tc (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightConv F φ f, hφ'⟩)
    (g : AdelicGL2 (𝓞 F) F) (hg : g ∈ finiteAdelicGL2Subgroup F) (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (h1 : ∀ i, ∃ u' ∈ U, ∃ u'' ∈ U, reps i = u' * g * u'')
    (h2 : ∀ x : AdelicGL2 (𝓞 F) F, (∃ u' ∈ U, ∃ u'' ∈ U, x = u' * g * u'') → ∃ i, ∃ u' ∈ U, x = reps i * u')
    (h3 : ∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ), S.comp Tc = Tc.comp S ∧
      ∀ φ : ↥(cuspMemberSubmodule F Φ₀ ξ),
        (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ Representation.invariants ((rightRegular F).comp U.subtype) →
        ∃ h : (fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i)) ∈ cuspMemberSubmodule F Φ₀ ξ,
          S (toCuspSubcarrier F hΦ₀ σ ξ φ) = toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∑ i, (φ : AdelicGL2 (𝓞 F) F → ℂ) (x * reps i), h⟩ := by sorry
