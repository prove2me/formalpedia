-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
-- name    : AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/c1fd4817-7f2b-57c0-8269-d008b77f4698
-- title:
--   Dichotomy for classes of a typed level cut in L
-- statement:
--   Let $F$ be a number field, $\alpha,\beta\in\mathbb R$ and $\Phi_0\subseteq \mathrm{GL}_2(\mathbb A_F)$ with $0<\alpha<\beta$, $\Phi_0$ contained in the slab where the idele norm of the determinant lies in $[\alpha,\beta]$ and $\Phi_0$ a fundamental domain for the image of $\mathrm{GL}_2(F)$ acting on that slab for the restricted adelic Haar measure. Let $\sigma\in\mathbb R$ and let $\xi$ be a character of the full group of idele units with $\|\xi(z)\|=\|z\|^{\sigma}$. Let $M$ be a submodule of the cuspidal subcarrier `cuspSubcarrier F hΦ₀ σ ξ` (the closure inside $L^2$ of the weighted measure of the classes of continuous smooth cuspidal automorphic members) which satisfies `IsIrreducibleCuspSubrep`: it is closed, stable under the cusp lifts of right translations by finite-adelic elements, of right translations by archimedean row isometries and of right convolutions by factorizable archimedean bi-finite test functions, it is nonzero, and every closed cuspidal subrepresentation contained in it is $0$ or all of it. Let $U$ be a compact subgroup and $O$ an open subgroup of $\mathrm{GL}_2(\mathbb A_F)$ with $U=O\cap\ker(\mathrm{gl}_{\mathrm{arch}})$, and let `tys` be a finite family of archimedean types, one finite list of row-isometry representations at each infinite place. Let $Y$ be a submodule of complex functions on $\mathrm{GL}_2(\mathbb A_F)$ consisting of continuous smooth cuspidal automorphic members for the pins of $\Phi_0$ and $\xi$, such that the class in the cuspidal subcarrier of every element of $Y$ lies in $M$, every $\psi\in Y$ satisfies $\psi(gk)=\psi(g)$ for all $g$ and all $k\in U$, and $Y$ lies in the archimedean cut submodule of `tys`. Finally let $L$ be a closed submodule of the cuspidal subcarrier, and write $N$ for the space of continuous cuspidal members whose class lies in $L$; assume $N$ is stable under right translation by the images of row isometries at each infinite place; that for each $g$ in the finite-adelic subgroup and each finite family $\mathrm{reps}:\mathrm{Fin}\,n\to\mathrm{GL}_2(\mathbb A_F)$ of elements of $UgU$ forming a system of representatives for the right $U$-cosets in $UgU$, pairwise inequivalent modulo right multiplication by $U$, every $\varphi\in N$ that is invariant under the right regular action of $U$ has $x\mapsto\sum_i\varphi(x\,\mathrm{reps}_i)$ in $N$; and that $N$ is stable under right convolution by every factorizable test function that is archimedean bi-finite of type `tys` and bi-invariant under $U$. Then the submodule of classes of elements of $Y$ either meets $L$ in $0$ or is contained in $L$.
--
--   This is the Hilbert-space form of the irreducibility transfer for cuspidal spectra: irreducibility of the closed cuspidal subrepresentation $M$ forces the image of a $(U,\mathtt{tys})$-cut space $Y$ of cuspidal members of $M$ to be either disjoint from, or contained in, any closed subspace $L$ whose pull-back to cuspidal members is stable under archimedean translations, Hecke double-coset sums at level $U$ and right convolutions by $U$-bi-invariant test functions of the given archimedean type. It is used in the proof of the corresponding dichotomy for the orthogonal complement of $L$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed.lean

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

theorem AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hL : IsClosed (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hLk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L),
        rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L) ⊓ Representation.invariants ((rightRegular F).comp U.subtype),
        (fun x => ∑ i, φ (x * reps i)) ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLconv : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F h → IsArchBiFinite F tys h →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L), rightConv F φ h ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L)) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓ L = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤ L := by sorry
