-- Prove2me | Theorems.Thm_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
-- name    : AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/3654e88a-2453-522f-b177-57cedf222ab6
-- title:
--   Bruhat relation at one finite place for induced sections
-- statement:
--   Let $F$ be a number field, and let $\alpha \colon (\mathbb{A}_F)^\times \to \mathbb{R}^\times$ be the homomorphism obtained from the module character `distribHaarChar` of the adele ring $\mathbb{A}_F =$ `AdeleRing (𝓞 F) F`, pushed from $\mathbb{R}_{\ge 0}$ into $\mathbb{R}$ and regarded as a map into units. Assume $\alpha$ takes strictly positive values, fix $s \in \mathbb{C}$, and let $\varphi \colon \mathrm{GL}_2(\mathbb{A}_F) \to \mathbb{C}$ satisfy `IsInducedSection` for the characters $\chi_1 = 1 \cdot$ `cpowChar` $\alpha$ with exponent $s + 1/2$ and $\chi_2 = 1 \cdot$ `cpowChar` $\alpha$ with exponent $-(s+1/2)$; that is, $\varphi(bg) = \chi_1(b_{00})\,\chi_2(b_{11})\,\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup (lower-left entry zero). Let $v$ be a height one prime of $\mathcal{O}_F$ and $x \in \mathbb{A}_F$ an adele whose finite component at $v$ is nonzero, and let $x'$ be $x$ with that component replaced by $(x_v)^{-1}$ (the infinite part and all other finite components unchanged). Writing $w$ for the image in $\mathrm{GL}_2(\mathbb{A}_F)$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $F$, $n(y) = \begin{pmatrix}1&y\\0&1\end{pmatrix}$, and $w_v$ for the adelic matrix equal to that antidiagonal matrix in the $v$-component and to the identity in all other components, the conclusion is $$\varphi\bigl(w^{-1} n(x)\, w_v\bigr) = \bigl(\mathrm{modulus}(x_v)\bigr)^{-(2s+1)}\,\varphi\bigl(w^{-1} n(x')\bigr),$$ where $\mathrm{modulus}(x_v)$ is the Haar module of multiplication by $x_v$ on the completion $F_v$, viewed as a real number and raised to a complex power.
--
--   This is the Bruhat-type relation at a single finite place which underlies the change of variables $x_v \mapsto x_v^{-1}$ in the local intertwining integral attached to the Weyl element. It is used in the analysis of the Weyl intertwining integral of a flat family of induced sections near $s = 1/2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm
open scoped NNReal

theorem AutomorphicForm.apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (v : HeightOneSpectrum (𝓞 F)) (x : AdeleRing (𝓞 F) F) (_hx : x.2 v ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (x.1, AdelicDock.splice (𝓞 F) F v x.2 (x.2 v)⁻¹)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x
          * AdelicDock.finEmbed (𝓞 F) F (AdelicDock.localEmbed (𝓞 F) F v gl2Weyl))
      = (((LanglandsTunnell.TateLocal.modulus (x.2 v) : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by sorry
