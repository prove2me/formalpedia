-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
-- name    : AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/4d924634-333a-5fd6-9bcf-657a32007847
-- title:
--   Central eigenvalue bᵥ shifts the Whittaker coefficients
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\Psi$ a Hecke eigensystem over $\mathbb{C}$ for $F$, that is a datum of a nonzero level ideal of $\mathcal{O}_F$ together with families $a$ and $b$ indexed by the finite places. Let $R$ be a smooth cusp realisation of $\Psi$ at the production pins attached to $D$, with level subgroups $N \mapsto \mathrm{levelOne}(N) \cap \ker(\text{archimedean projection})$, Hecke generators $v \mapsto \mathrm{heckeGen}(v)$ and the adelic box as conditioning set: so $R$ carries a function $R.\mathrm{toFun} : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$, nonvanishing somewhere, a central character on $Z = \top$, the predicate `IsSmoothCuspAutomorphicFnAt`, invariance under the level subgroup at $\Psi$'s level, a finite exceptional set of places, the Hecke eigenfunction property with eigenvalue $a_v$ and the central relation $R.\mathrm{toFun}(z_v \cdot g) = b_v\, R.\mathrm{toFun}(g)$ for $z_v$ the central scalar of $\det(\mathrm{heckeGen}(v))$, both away from the exceptional set. Let $\psi$ be an additive character of $\mathbb{A}_F$ with values in $\mathbb{C}$, let $v$ be a finite place outside $R.\mathrm{exceptionalSet}$, let $\varpi$ lie in the valuation ring at $v$ with nonzero image $\pi$ in $F_v$, and assume that $\mathrm{diag}(\pi,1)$, embedded at $v$ into $\mathrm{GL}_2(\mathbb{A}_F)$, equals $\mathrm{heckeGen}(v)$. Then for every $\alpha \in F$ and every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the Whittaker coefficient $W_\alpha(h) = \int R.\mathrm{toFun}(n(x)h)\,\psi(-\alpha x)\,d\nu(x)$, taken with respect to the Haar measure on $\mathbb{A}_F$ conditioned on the adelic box, satisfies $W_\alpha\big(g \cdot \iota_v(\mathrm{diag}(\pi,\pi))\big) = b_v\, W_\alpha(g)$, where $\iota_v$ is the embedding of $\mathrm{GL}_2(F_v)$ at $v$.
--
--   This is the transfer of the central-character relation of an automorphic function to each of its Whittaker coefficients: translating on the right by the scalar matrix $\pi$ placed at $v$ multiplies $W_\alpha$ by the central eigenvalue $b_v$. It serves as the central-shift input to the unramified torus recursion for Whittaker functions, and is used in the construction of the Euler product for twisted $L$-series of arithmetically genuine cusp realisations and in the translate-covering estimate.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient.lean

import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_NumberField_AdelicBox

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm LocalGL2 AdelicDock
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.AdelicBox AutomorphicForm.SiegelCovering

theorem AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_mul_placeEmbed_scalarPi_eq_b_mul_whittakerCoefficient
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hgen : finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (diagPi ϖ hϖ0)) = heckeGen (𝓞 F) F v)
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.scalarPi
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.b v * whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by sorry
