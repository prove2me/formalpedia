-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent
-- name    : CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.38243+00:00
-- url     : https://prove2.me/theorems/ffe96ab2-d515-51c5-ba4a-02c1f1ad04a4
-- title:
--   Drinfeld's standard special formal mathcal O_D-module of height four
-- statement:
--   Let $p$ be a prime and write $\mathbb Z_{p^2}$ for [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements. The assertion is that there exists an object $X_0$ of [`CerednikDrinfeld.FormalODModule p (CerednikDrinfeld.Zp2 p)`](def/CerednikDrinfeld_SpecialFormalModule.html#L170), that is: a two-variable formal group law $F$ over $\mathbb Z_{p^2}$ which is commutative, together with a family of pairs of power series $\mathrm{act}(a)$ indexed by $a \in \mathbb Z_{p^2}$ and a further pair $\varpi$, each an endomorphism of $F$ (constant coefficients zero and compatible with $F$ in both arguments), such that $\mathrm{act}(1)$ is the identity, $\mathrm{act}(ab)$ is the composite of $\mathrm{act}(a)$ with $\mathrm{act}(b)$, $\mathrm{act}(a+b)$ is the sum of $\mathrm{act}(a)$ and $\mathrm{act}(b)$ formed via $F$, $\varpi \circ \varpi = \mathrm{act}(p)$ and $\varpi \circ \mathrm{act}(a) = \mathrm{act}(\sigma a) \circ \varpi$ for the Witt vector Frobenius $\sigma$; and such that $X_0$ has the following universal property: for every commutative ring $B$ and every ring homomorphism $j : \mathbb Z_{p^2} \to B$ for which the image of $p$ in $B$ is nilpotent, the coefficientwise base change $X_0.\mathrm{map}\,j$ satisfies both `IsSpecial j` and `HasHeight 4`. Here `IsSpecial j` says that inside the Lie module of $X_0.\mathrm{map}\,j$ the two submodules $\bigcap_a \ker(\mathrm{lieAct}(a) - j(a))$ and $\bigcap_a \ker(\mathrm{lieAct}(a) - j(\sigma a))$ are complementary and each is an invertible $B$-module, and `HasHeight 4` is the predicate `HasKernelOfDegree` applied to the endomorphism $\mathrm{act}(p)$ of the base-changed law and the integer $p^4$.
--
--   This is the existence of Drinfeld's standard special formal $\mathcal O_D$-module of height $4$ and dimension $2$ over $\mathbb Z_{p^2}$, the base point used in the Čerednik–Drinfeld description of $p$-adic uniformisation. It supplies the nonemptiness input for the moduli statements [`CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover`](thm.html#CerednikDrinfeld.SpecialFormal.Rigidified.exists_moduliPackage_isZariskiSheaf_eta_iff_isIsomorphic_and_natural_and_cover) and [`CerednikDrinfeld.SpecialFormal.exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing`](thm.html#CerednikDrinfeld.SpecialFormal.exists_isSpecial_and_hasHeight_four_and_isZariskiSheaf_wittVector_of_isNoetherianRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_forall_isSpecial_map_and_hasHeight_four_map_of_isNilpotent
    (p : ℕ) [Fact p.Prime] :
    ∃ X₀ : CerednikDrinfeld.FormalODModule p (CerednikDrinfeld.Zp2 p),
      ∀ (B : Type u) [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B), IsNilpotent (p : B) →
        (X₀.map j).IsSpecial j ∧ (X₀.map j).HasHeight 4 := by sorry
