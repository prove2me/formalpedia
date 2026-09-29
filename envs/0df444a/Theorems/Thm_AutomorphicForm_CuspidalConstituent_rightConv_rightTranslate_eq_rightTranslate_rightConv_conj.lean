-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
-- name    : AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/53054e53-6473-5d0a-9cee-858f981345da
-- title:
--   Right convolution versus right translation on adelic GL₂
-- statement:
--   Let $F$ be a number field, so that $\mathrm{GL}_2(\mathbb{A}_F)$ denotes the general linear group of degree $2$ over the adele ring of $F$ (formed from the ring of integers $\mathcal{O}_F$ and $F$), equipped with its Borel $\sigma$-algebra and the Haar measure $\mu$ on that group. For $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and $\varphi, f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ write $(\varphi * f)(g) = \int \varphi(g x) f(x)\, d\mu(x)$ for the right convolution and $(R(h)\varphi)(x) = \varphi(x h)$ for right translation by $h$. The assertion is that for every $h \in \mathrm{GL}_2(\mathbb{A}_F)$ and all functions $\varphi, f : \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ one has the equality of functions
--   $$(R(h)\varphi) * f = R(h)\bigl(\varphi * f^{h}\bigr), \qquad f^{h}(y) = f(h y h^{-1}).$$
--   No measurability, integrability or growth hypothesis is imposed on $\varphi$ or $f$: the identity is asserted for arbitrary complex-valued functions, the Bochner integrals being interpreted as zero when the integrand is not integrable.
--
--   This is the elementary compatibility of right convolution with the right regular action, the conjugated test function $f^h$ accounting for the translation; it rests on the bi-invariance (unimodularity) of the Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$. It is used to show that the cyclic span of an automorphic form, and of its translates, is stable under right convolution, and is cited in the construction of cuspidal subrepresentations and in the treatment of spherical vectors of a given level type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_rightConv_rightTranslate_eq_rightTranslate_rightConv_conj.lean

import Definitions.Def_AutomorphicForm_CuspidalConstituent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj
    (F : Type) [Field F] [NumberField F]
    (h : AdelicGL2 (𝓞 F) F) (φ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (rightTranslate F h φ) f = rightTranslate F h (rightConv F φ (fun y => f (h * y * h⁻¹))) := by sorry
