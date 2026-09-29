-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist
-- name    : AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/acfc62ed-faca-55b8-8e9b-f22d9bf5e889
-- title:
--   Twisting a cuspidal constituent by a finite-order Hecke character
-- statement:
--   Let $F$ be a number field, let $D \subseteq \mathrm{GL}_2(\mathbb{A}_F)$, let $U$ assign to each ideal of $\mathcal{O}_F$ a subgroup of $\mathrm{GL}_2(\mathbb{A}_F)$, let $gen$ assign to each height-one prime of $\mathcal{O}_F$ an element of $\mathrm{GL}_2(\mathbb{A}_F)$, and let $B \subseteq \mathbb{A}_F$. These data give the carrier `productionPinsOf F D U gen B`, whose measure-theoretic data are the Borel $\sigma$-algebra and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, the Borel $\sigma$-algebra on $\mathbb{A}_F$ together with the additive Haar measure conditioned on $B$, whose centre group is the full group $\mathbb{A}_F^\times$ of ideles, and whose window, level family and generators are $D$, $U$, $gen$. Let $\xi$ be a homomorphism from that centre group to $\mathbb{C}^\times$, and let $\eta : \mathbb{A}_F^\times \to \mathbb{C}^\times$ be a character that is trivial on the principal ideles, continuous and of finite order. Let $V$ be a $\mathbb{C}$-submodule of the functions $\mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ which is a cuspidal constituent for $\xi$ at these pins, i.e. $V$ is contained in `cuspKFiniteSubmodule F (productionPinsOf F D U gen B) ξ`, is stable under right translation by elements of `finiteAdelicGL2Subgroup F`, under right translation by `rowIsometryInclAt₀ F w k` for every infinite place $w$ and every $k$ in `rowIsometrySubgroup₀ w.Completion`, and under right convolution by functions $f$ satisfying `IsFactorizableTestFn F f` and `IsArchBiFinite F tys f`; moreover $V \neq 0$ and every such subspace contained in $V$ is $0$ or $V$. Then the $\mathbb{C}$-span of $\{g \mapsto \eta(\det g)\,\varphi(g) : \varphi \in V\}$ is again a cuspidal constituent at the same pins, for the character $z \mapsto \xi(z)\,\eta(z)^2$.
--
--   This is the function-level form of the statement that tensoring by $\eta \circ \det$ permutes the cuspidal automorphic representations of $\mathrm{GL}_2$, the central character being shifted by $\eta^2$. It is used when comparing a cuspidal constituent with its twists, in particular in the finite-dimensionality statement [`AutomorphicForm.CuspidalConstituent.IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq`](thm.html#AutomorphicForm.CuspidalConstituent.IsCuspConstituent.finiteDimensional_of_forall_rightTranslate_eq) and in the existence statement [`AutomorphicForm.CuspidalConstituent.exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd`](thm.html#AutomorphicForm.CuspidalConstituent.exists_cuspConstituentMeets_span_image_fnTwist_of_isIsotypicCuspFormAt_of_isBoundedGenuineFn_of_forall_not_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_isCuspConstituent_twistedCentralChar_span_image_fnTwist.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_HeckeCharacter_FiniteOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.isCuspConstituent_twistedCentralChar_span_image_fnTwist
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (η : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hη : HeckeCharacter.IsFiniteOrderHeckeChar F η)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F D U gen B) ξ V) :
    IsCuspConstituent F (productionPinsOf F D U gen B) (twistedCentralChar F _ ξ η)
      (Submodule.span ℂ ((fun φ => fnTwist F η φ) '' (V : Set (AdelicGL2 (𝓞 F) F → ℂ)))) := by sorry
