-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient_principal
-- name    : AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient_principal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b1a9b080-e025-5ad5-8bb7-4d29aea075bc
-- title:
--   Central uniformizer scalar at a good place scales Whittaker coefficients
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\Psi$ a complex Hecke eigensystem for $F$, i.e. a nonzero level ideal of $\mathcal{O}_F$ together with families $a_v, b_v \in \mathbb{C}$ indexed by the height-one primes of $\mathcal{O}_F$. Let $R$ be a smooth cusp realization of $\Psi$ at the production pins built from $D$, the level subgroups $N \mapsto \mathtt{principalLevel}(N) \sqcap \ker(\mathrm{glArch})$, the Hecke generators $v \mapsto \mathtt{heckeGen}(v)$ and the adelic box; thus $R$ carries a function $\varphi = R.\mathtt{toFun} : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is not identically zero, is invariant under right translation by the level subgroup at $\Psi$'s level, satisfies the smooth cusp condition with respect to a central character on $Z = \top$, and, for every $v$ outside a finite exceptional set, is a Hecke coset eigenfunction with eigenvalue $a_v$ and satisfies $\varphi(z_v y) = b_v\,\varphi(y)$ for all $y$, where $z_v$ is the central scalar matrix attached to $\det \mathtt{heckeGen}(v)$. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, and write $W_\alpha(g) = \int \varphi(n(x) g)\,\psi(-(\alpha x))\,d\nu(x)$ for the associated Whittaker coefficient, the integral being taken against the additive adelic Haar measure conditioned on the adelic box. Let $v$ be a height-one prime outside $R$'s exceptional set, let $\varpi$ lie in the valuation ring of $F_v$ with nonzero image $\varpi \in F_v$, and assume that the image of $\mathrm{diag}(\varpi,1) \in \mathrm{GL}_2(F_v)$ under the embedding $\mathrm{GL}_2(F_v) \to \mathrm{GL}_2(\mathbb{A}_F^{\mathrm{fin}}) \to \mathrm{GL}_2(\mathbb{A}_F)$ equals $\mathtt{heckeGen}(v)$. Then for all $\alpha \in F$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$, $W_\alpha\bigl(g \cdot \iota_v(\varpi I_2)\bigr) = b_v \, W_\alpha(g)$, where $\iota_v$ is that same embedding and $\varpi I_2 = \mathrm{diag}(\varpi,\varpi)$.
--
--   This is the elementary transfer of the central eigenvalue relation of an automorphic form to each of its Whittaker coefficients: a central element may be pushed past the unipotent integration. It supplies the central-scalar input to the unramified Whittaker recursion at a good place, and is used downstream in the estimate comparing a function with finitely many translates of itself over a Siegel covering at principal level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient_principal.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicBox AutomorphicForm.SiegelCovering

theorem AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.b v * whittakerCoefficient F
        (productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by sorry
