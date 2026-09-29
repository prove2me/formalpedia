-- Prove2me | Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image
-- name    : CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:58.660386+00:00
-- url     : https://prove2.me/theorems/7304df00-8d13-525b-a2f5-b5a85a7ef87d
-- title:
--   Base change of the Lie eigenspace decomposition
-- statement:
--   Let $p$ be a prime, $B$ a commutative ring, $j\colon \mathbb{Z}_{p^2} = W(\mathbb{F}_{p^2}) \to B$ a ring homomorphism (here $\mathbb{Z}_{p^2}$ is [`CerednikDrinfeld.Zp2 p`](def/CerednikDrinfeld_SpecialFormalModule.html#L17), the Witt vectors of the field with $p^2$ elements), and let $X$ be a formal $\mathcal{O}_D$-module over $B$ in the sense of the structure `FormalODModule`: a commutative $2$-dimensional formal group law $F$ over $B$, an action $a \mapsto X.\mathrm{act}\,a$ of $\mathbb{Z}_{p^2}$ by endomorphisms of the law which is multiplicative, additive and sends $1$ to the identity, together with an endomorphism $\varpi$ of the law satisfying $\varpi \circ \varpi = [p]$ and $\varpi \circ [a] = [\sigma a] \circ \varpi$ for the Witt Frobenius $\sigma$. On the Lie module of $X$ let $a$ act by the matrix $\mathrm{lieAct}$ given by the linear part of $X.\mathrm{act}\,a$, and put $(\mathrm{Lie}\,X)_0 = \bigcap_a \ker(\mathrm{lieAct}\,a - j(a)\,\mathrm{id})$ and $(\mathrm{Lie}\,X)_1 = \bigcap_a \ker(\mathrm{lieAct}\,a - j(\sigma a)\,\mathrm{id})$, the submodules `lieZero j` and `lieOne j`. Assume these two submodules are complementary, i.e. $\mathrm{Lie}\,X = (\mathrm{Lie}\,X)_0 \oplus (\mathrm{Lie}\,X)_1$. Then for every ring homomorphism $f\colon B \to B'$ of commutative rings, the corresponding submodules of the base-changed formal $\mathcal{O}_D$-module `X.map f` over $B'$, formed with respect to $f \circ j$, are again complementary, and each of them is the $B'$-span of the image of the corresponding submodule of $\mathrm{Lie}\,X$ under $v \mapsto f \circ v$ on $\mathrm{Fin}\,2 \to B$.
--
--   This is the functoriality in the base of the grading of the Lie algebra of a formal $\mathcal{O}_D$-module by the two characters of $\mathbb{Z}_{p^2}$, the first half of Drinfeld's condition that such a module be special. It is used to transport the graded structure along base change, and is cited in the analysis of critical charts and in the decomposition of base-changed Lie elements as sums of Verschiebung iterates of homotheties.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_FormalODModule_isCompl_lieZero_lieOne_map_and_eq_span_image.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.isCompl_lieZero_lieOne_map_and_eq_span_image
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j))
    {B' : Type u} [CommRing B'] (f : B →+* B') :
    IsCompl ((X.map f).lieZero (f.comp j)) ((X.map f).lieOne (f.comp j)) ∧
    (X.map f).lieZero (f.comp j) =
      Submodule.span B' ((fun v : Fin 2 → B => ⇑f ∘ v) '' (X.lieZero j : Set (Fin 2 → B))) ∧
    (X.map f).lieOne (f.comp j) =
      Submodule.span B' ((fun v : Fin 2 → B => ⇑f ∘ v) '' (X.lieOne j : Set (Fin 2 → B))) := by sorry
