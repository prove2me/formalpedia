-- Prove2me | Theorems.Thm_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
-- name    : AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/907faf44-9296-5b09-bfb4-e0ff648a1e41
-- title:
--   Bruhat–Möbius relation at one archimedean place
-- statement:
--   Let $F$ be a number field and let $\alpha\colon \mathbb{A}_F^\times \to \mathbb{R}^\times$ be the unit-valued homomorphism obtained from the Haar-module character `distribHaarChar` of the adele ring $\mathbb{A}_F$ followed by the inclusion $\mathbb{R}_{\ge 0}\hookrightarrow\mathbb{R}$. Assume $\alpha(t)>0$ for all $t$, fix $s\in\mathbb{C}$, and let $\varphi\colon \mathrm{GL}_2(\mathbb{A}_F)\to\mathbb{C}$ satisfy `IsInducedSection` for the pair of characters $\alpha^{s+1/2}$ and $\alpha^{-(s+1/2)}$ (the `etaFst`/`etaSnd` characters with trivial $\mu,\nu$): that is, $\varphi(bg)=\alpha(b_{00})^{s+1/2}\,\alpha(b_{11})^{-(s+1/2)}\varphi(g)$ for every $g$ and every $b$ in the adelic Borel subgroup, i.e. with $b_{10}=0$, where $b_{00},b_{11}$ are taken as ideles. Let $w$ be an infinite place of $F$ and let $k\in \mathrm{GL}_2(\mathbb{A}_F)$ have trivial finite part and trivial archimedean component at every place $w'\ne w$; write $k_w=\begin{pmatrix}a&b\\ c&d\end{pmatrix}$ for its component at $w$. Let $x\in\mathbb{A}_F$ with $a+x_w c\ne 0$, and let $x'$ be the adele agreeing with $x$ at all places except $w$, where $x'_w=(b+x_w d)/(a+x_w c)$. Then, with $\omega$ the image of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $n(\cdot)$ the upper unipotent matrix, $$\varphi\big(\omega^{-1} n(x) k\big)=\big(\|\det k_w\|^{m_w}\big)^{s+1/2}\big(\|a+x_w c\|^{m_w}\big)^{-(2s+1)}\varphi\big(\omega^{-1} n(x')\big),$$ where $m_w=[F_w:\mathbb{R}]$ and the complex powers are of the indicated real numbers.
--
--   This is the Bruhat–Möbius relation at a single archimedean place: right translation of a section of the induced representation by an element supported at $w$ multiplies its value on the open Bruhat cell by the local factor $\|\det k_w\|_w^{s+1/2}\|a+x_wc\|_w^{-(2s+1)}$ and replaces $x_w$ by its Möbius image. It feeds the analysis of the Weyl intertwining integral for the flat family, used in the limit statement [`AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt`](thm.html#AutomorphicForm.tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply.lean

import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology
open scoped NNReal
open scoped Classical in

theorem AutomorphicForm.apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
      (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (w : InfinitePlace F) (k : AdelicGL2 (𝓞 F) F)
      (_hkf : glFin (𝓞 F) F k = 1)
      (_hka : ∀ w' : InfinitePlace F, w' ≠ w → archComponent F w' (glArch (𝓞 F) F k) = 1)
      (x : AdeleRing (𝓞 F) F),
    let kw : Matrix (Fin 2) (Fin 2) w.Completion := (archComponent F w (glArch (𝓞 F) F k) : GL (Fin 2) w.Completion)
    ∀ (_hx : kw 0 0 + x.1 w * kw 1 0 ≠ 0),
    let x' : AdeleRing (𝓞 F) F := (Function.update x.1 w ((kw 0 1 + x.1 w * kw 1 1) / (kw 0 0 + x.1 w * kw 1 0)), x.2)
    φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * k)
      = (((‖kw.det‖ ^ w.mult : ℝ)) : ℂ) ^ (s + 1 / 2)
        * (((‖kw 0 0 + x.1 w * kw 1 0‖ ^ w.mult : ℝ)) : ℂ) ^ (-(2 * s + 1))
        * φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x') := by sorry
