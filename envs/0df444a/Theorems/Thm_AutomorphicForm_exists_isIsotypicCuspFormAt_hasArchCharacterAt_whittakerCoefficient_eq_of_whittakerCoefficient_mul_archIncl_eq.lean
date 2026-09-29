-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
-- name    : AutomorphicForm.exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/a434f863-ed4e-5311-ba08-b6c0cfffb278
-- title:
--   Weight-n projection of an isotypic cusp form at a real place
-- statement:
--   Let $F$ be a number field, $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ a set, and $w$ a real infinite place of $F$. Assume $D$ is stable under right multiplication by the images under `adelicArchGLInclAt F w` of the elements of `rowIsometrySubgroup₀ w.Completion`, and that $D$ is measurable for the Borel structure `glBorel` on $\mathrm{GL}_2(\mathbb{A}_F)$. Work with the carrier pins `productionPinsOf` attached to $D$, whose measure is the adelic Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, whose central subgroup is all of $\mathbb{A}_F^\times$, whose level subgroups are $\mathrm{levelOne}(N)$ intersected with the kernel of the archimedean projection, whose Hecke generators are `heckeGen`, and whose additive measure is the adelic additive Haar measure conditioned on `adelicBox F`. Let $\xi$ be a character of that central subgroup with values in $\mathbb{C}^\times$, $N$ an ideal of $\mathcal{O}_F$, $S$ a finite set of finite places, $\Psi$ a Hecke eigensystem over $\mathbb{C}$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsIsotypicCuspFormAt` for these data: it is a smooth cuspidal automorphic function for the pins and $\xi$, is continuous, is right invariant under the level subgroup at $N$, is a Hecke coset eigenfunction with eigenvalue $\Psi.a\,v$ at each $v \notin S$, and satisfies the central relation $\varphi(\mathrm{diag}(\det \mathrm{gen}_v) g) = \Psi.b\,v \cdot \varphi(g)$ for $v \notin S$. Let $n \in \mathbb{Z}$, let $\psi$ be a continuous additive character of $\mathbb{A}_F$, write $\chi$ for the character of `rowIsometrySubgroup₀ w.Completion` obtained by composing `archWeightCharℝ n` with the transport `rowIsometrySubgroup₀Map` along the isomorphism $F_w \cong \mathbb{R}$ furnished by $w$ being real, and let $A \subseteq \mathrm{GL}_2(\mathbb{A}_F)$ be a set on which the Whittaker coefficient of $\varphi$ at $\alpha = 1$, namely $g \mapsto \int \varphi(u(x) g)\,\psi(-x)\,d\nu(x)$ for the conditioned additive measure $\nu$, already transforms by $\chi$ under right multiplication by the embedded subgroup. Then there exists $\varphi'$ which again satisfies `IsIsotypicCuspFormAt` for the same pins, $\xi$, $N$, $S$ and $\Psi$, which satisfies `HasArchCharacterAt₀ F w χ φ'`, expressing that $\varphi'$ transforms by $\chi$ under right translation by `rowIsometrySubgroup₀ w.Completion` embedded at $w$, and whose Whittaker coefficient at $\alpha = 1$ agrees with that of $\varphi$ at every $g \in A$.
--
--   This is the $\mathrm{SO}(2)$-isotypic projection (weight-$n$ $K$-type projector) at a real place, stated function-theoretically: averaging against the character $\chi$ preserves all the clauses defining an isotypic cusp form and commutes with the Whittaker integral, so the first Whittaker coefficient is untouched on any set where it already has weight $n$. It is used in the Langlands–Tunnell part of the argument to replace a cusp form by one of prescribed archimedean weight without changing its Whittaker data, for instance in the analysis of Casimir eigenvectors of minimal weight.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_isIsotypicCuspFormAt_hasArchCharacterAt_whittakerCoefficient_eq_of_whittakerCoefficient_mul_archIncl_eq
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (w : InfinitePlace F) (hw : w.IsReal)
    (hD : ∀ g ∈ D, ∀ κ : rowIsometrySubgroup₀ w.Completion,
      g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion) ∈ D)
    (hDm : @MeasurableSet (AdelicGL2 (𝓞 F) F) (NumberField.AdelicHaar.glBorel (Fin 2) (𝓞 F) F) D)
    (ξ : (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ)
    (n : ℤ) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : Continuous ψ)
    (A : Set (AdelicGL2 (𝓞 F) F))
    (hWA : ∀ g ∈ A, ∀ κ : rowIsometrySubgroup₀ w.Completion,
      whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 (g * adelicArchGLInclAt F w (κ : GL (Fin 2) w.Completion))
        = (((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) κ : ℂ) * whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 g) :
    ∃ φ' : AdelicGL2 (𝓞 F) F → ℂ,
      IsIsotypicCuspFormAt F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ N S Ψ φ' ∧
      HasArchCharacterAt₀ F w ((archWeightCharℝ n).comp (rowIsometrySubgroup₀Map (ringEquivRealOfIsReal hw) (norm_ringEquivRealOfIsReal hw))) φ' ∧
      ∀ g ∈ A, whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ' 1 g = whittakerCoefficient F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ φ 1 g := by sorry
