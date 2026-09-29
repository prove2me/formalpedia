-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
-- name    : AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b54a8f62-9283-510b-b098-d0afd7d7f667
-- title:
--   Hecke eigenvalue relation for Whittaker coefficients at a good place
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\Psi$ a complex Hecke eigensystem for $F$, i.e. a nonzero level ideal $\Psi.\mathrm{level}$ of $\mathcal{O}_F$ together with families $a_v, b_v \in \mathbb{C}$ indexed by the finite places. All data are taken at the pins `productionPinsOf F D …`: the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, window $D$, central subgroup $\top$, level subgroups $N \mapsto \mathrm{levelOne}(N) \sqcap \ker(\mathrm{glArch})$ (the level-one congruence subgroup intersected with the kernel of the projection to $\mathrm{GL}_2$ of the infinite adeles), Hecke generators $\mathrm{heckeGen}(v)$, and, for the integration variable, the additive Haar measure on $\mathbb{A}_F$ conditioned on the adelic box. Let $R$ be a smooth cusp realisation at these pins for $\Psi$, with underlying function $\varphi = R.\mathrm{toFun}$, and let $\psi$ be an additive character of $\mathbb{A}_F$ such that for all $\alpha \in F$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$ the function $x \mapsto \varphi(n(x)g)\,\psi(-\alpha x)$, with $n(x) = \begin{pmatrix}1&x\\0&1\end{pmatrix}$, is integrable for that measure; write $W_\alpha(g)$ for its integral, the Whittaker coefficient. Let $v$ be a finite place outside the finite exceptional set of $R$, let $\varpi$ lie in the valuation ring of $F_v$ with nonzero image $\pi$ in $F_v$, let $I$ be a finite type with $\#I = |\mathcal{O}_F/v|$, and $b : I \to \mathcal{O}_v$. Assume that the family indexed by $\mathrm{Option}\,I$ whose value at `none` is the image in $\mathrm{GL}_2(\mathbb{A}_F)$, under the embedding placing a matrix at $v$ and $1$ elsewhere, of $w\,\mathrm{diag}(\pi,1)\,w$ and whose value at `some c` is the image of $\begin{pmatrix}1&b_c\\0&1\end{pmatrix}\mathrm{diag}(\pi,1)$ is a Hecke coset system for the level subgroup $\mathrm{levelOne}(\Psi.\mathrm{level}) \sqcap \ker(\mathrm{glArch})$ and the element $\mathrm{heckeGen}(v)$: each member lies in the double coset $U\,\mathrm{heckeGen}(v)\,U$, every element of that double coset lies in the same left coset modulo $U$ as some member, and distinct indices give distinct cosets. Then for every $\alpha \in F$ and $g \in \mathrm{GL}_2(\mathbb{A}_F)$, $$\sum_{i \in I} W_\alpha\!\left(g\,\iota_v\begin{pmatrix}\pi & b_i\\0&1\end{pmatrix}\right) + W_\alpha\!\left(g\,\iota_v\begin{pmatrix}1&0\\0&\pi\end{pmatrix}\right) = a_v\, W_\alpha(g),$$ where $\iota_v$ is the same embedding $\mathrm{GL}_2(F_v) \to \mathrm{GL}_2(\mathbb{A}_F)$.
--
--   This is the statement that the Hecke operator at a good place commutes with the formation of Whittaker coefficients, written out in the explicit left-coset representatives $\begin{pmatrix}\pi&b\\0&1\end{pmatrix}$ and $\begin{pmatrix}1&0\\0&\pi\end{pmatrix}$ used in the unramified Whittaker computation. It feeds the derivation of the Euler product for the twisted $L$-function of an arithmetic genuine cusp realisation, and an approximation estimate for translates of such realisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient.lean

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm AutomorphicForm.SmoothCusp LocalGL2 AdelicDock
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar

theorem AutomorphicForm.SmoothCuspRealizationAt.sum_whittakerCoefficient_mul_placeEmbed_repSome_add_eq_a_mul_whittakerCoefficient
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) Ψ)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hint : ∀ (α : F) (g : AdelicGL2 (𝓞 F) F), WhittakerCoefficientIntegrable F
      (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ψ R.toFun α g)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ R.exceptionalSet)
    (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    {I : Type*} [Fintype I] (b : I → v.adicCompletionIntegers F)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 F) F Ψ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
      (fun i : Option I => finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
        (i.elim (localRepInf ϖ hϖ0) (fun c => localRepSome ϖ hϖ0 (b c))))))
    (α : F) (g : AdelicGL2 (𝓞 F) F) :
    (∑ i, whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
      whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α
        (g * UnramifiedWhittaker.placeEmbed F v (UnramifiedWhittaker.repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hϖ0)) =
      Ψ.a v * whittakerCoefficient F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) ψ R.toFun α g := by sorry
