-- Prove2me | Theorems.Thm_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
-- name    : AutomorphicForm.apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/a2e3b9a6-e137-573c-afc6-4f9cc90e8ca0
-- title:
--   Uniformiser scalars act by the raw central value bᵥ/cNorm(v)
-- statement:
--   Let $F$ be a number field, let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $B$ a subset of $\mathbb{A}_F$, and form the carrier data `productionPinsOf F D … B`, whose central subgroup is all of $\mathbb{A}_F^\times$, whose level groups are $U(M)=$ `levelOne` at $M$ intersected with the kernel of the archimedean projection, whose Hecke generators are `heckeGen` at each finite place, and whose measures are the adelic Haar measure on $\mathrm{GL}_2$ and the conditioning of the additive adelic Haar measure on $B$; let $\xi$ be a homomorphism from that central subgroup to $\mathbb{C}^\times$. Let $N$ be an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\Phi$ a Hecke eigensystem over $\mathbb{C}$ (a level, nonzero, together with families $a,b$ indexed by finite places), and $\varphi:\mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfying `IsIsotypicCuspFormAt` for these data: $\varphi$ satisfies `IsSmoothCuspAutomorphicFnAt` for $\xi$, is continuous, is right invariant under $U(N)$, is for every $v\notin S$ a Hecke coset eigenfunction at `heckeGen v` with eigenvalue $\Phi.a\,v$, and satisfies the central relation $\varphi(\mathrm{diag}$-scalar$(\det(\mathrm{heckeGen}\,v))\cdot g)=(\mathrm{cNorm}\,v)^{-1}\Phi.b\,v\cdot\varphi(g)$ for all $v\notin S$ and all $g$. Fix $v\notin S$ with $v\nmid N$ and $\varpi$ in the valuation ring at $v$ whose image in $F_v$ is nonzero of valuation $\exp(-1)$, i.e. any uniformiser. Then: first, for every $g\in\mathrm{GL}_2(\mathbb{A}_F)$, $\varphi(g\cdot \varpi I_2|_v)=(\mathrm{cNorm}\,v)^{-1}\Phi.b\,v\cdot\varphi(g)$, where $\varpi I_2|_v$ is the image under `placeEmbed` of the scalar matrix $\mathrm{diag}(\varpi,\varpi)\in\mathrm{GL}_2(F_v)$, i.e. $\varpi I_2$ at $v$ and $1$ at all other places; and second, if $\varphi$ is not identically zero, then $\xi$ evaluated at the idele unit which is $\varpi$ at $v$ and $1$ at all other finite places and trivial at the archimedean places equals $(\mathrm{cNorm}\,v)^{-1}\Phi.b\,v$ as a complex number.
--
--   This is the statement that, for an isotypic cusp form, the central character at a place outside the ramification set and away from the level is computed by the raw central entry of the eigensystem table, independently of the choice of uniformiser at $v$ — the eigensystem records the relation only at the determinant of the distinguished Hecke generator. It supplies the central-character input used in [`AutomorphicForm.shapedRaw_rawBundle_transl_rat`](thm.html#AutomorphicForm.shapedRaw_rawBundle_transl_rat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock AutomorphicForm UnramifiedWhittaker

theorem AutomorphicForm.apply_mul_placeEmbed_scalarPi_eq_toRawCentral_b_mul_of_isIsotypicCuspFormAt
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Φ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsIsotypicCuspFormAt F
      (productionPinsOf F D (fun M => levelOne (𝓞 F) F M ⊓ finiteAdelicGL2Subgroup F)
        (fun w => heckeGen (𝓞 F) F w) B) ξ N S Φ φ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) (hvN : ¬ v.asIdeal ∣ N)
    (ϖ : v.adicCompletionIntegers F)
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hϖ : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ)) :
    (∀ g : AdelicGL2 (𝓞 F) F,
        φ (g * placeEmbed F v (scalarPi (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) =
          Φ.toRawCentral.b v * φ g) ∧
    ((∃ g : AdelicGL2 (𝓞 F) F, φ g ≠ 0) →
      (((ξ.comp Subgroup.topEquiv.symm.toMonoidHom)
          (Units.map (finIncl (𝓞 F) F : FiniteAdeleRing (𝓞 F) F →* AdeleRing (𝓞 F) F)
            (localUnit (𝓞 F) F v (Units.mk0 _ hπ))) : ℂˣ) : ℂ) = Φ.toRawCentral.b v) := by sorry
