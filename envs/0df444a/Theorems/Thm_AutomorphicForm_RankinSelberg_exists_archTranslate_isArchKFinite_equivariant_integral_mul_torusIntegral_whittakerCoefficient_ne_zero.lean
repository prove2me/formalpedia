-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_archTranslate_isArchKFinite_equivariant_integral_mul_torusIntegral_whittakerCoefficient_ne_zero
-- name    : AutomorphicForm.RankinSelberg.exists_archTranslate_isArchKFinite_equivariant_integral_mul_torusIntegral_whittakerCoefficient_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/abc46293-f41d-5bb2-94dc-03174c82df69
-- title:
--   Non-vanishing of an archimedean Rankin–Selberg torus pairing
-- statement:
--   Let $K$ be a number field, $D_0$ a subset of $\mathrm{GL}_2(\mathbb A_K)$, let $\omega_x,\omega_y,\nu$ be homomorphisms from the idele group to $\mathbb C^\times$ and $w$ a real number, with $\|\omega_x(z)\|=\|\omega_y(z)\|=\mathrm{ideleNorm}(z)^w$, $\nu$ continuous, and $\omega_x(z)\overline{\omega_y(z)}\nu(z)=\mathrm{ideleNorm}(z)^{2w}$ for all ideles $z$. Let $x_0,y_1:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ be continuous, invariant under left multiplication by the image of $\mathrm{GL}_2(K)$, and transform under central scalars by $\omega_x$, respectively $\omega_y$. Write $W(\varphi)$ for `whittakerCoefficient` of $\varphi$ at $\alpha=1$ against the standard additive character, formed with the carrier pins `productionPinsOf` built from $D_0$, the level subgroups $\mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen`, and the box `adelicBox K`; thus $W(\varphi)(g)=\int \varphi(u(x)g)\,\psi(-x)$ against adelic additive Haar measure conditioned to that box. Assume, for each $g$ with identity archimedean part, each $k$ with identity finite part all of whose archimedean components are row isometries, and each idele $a$ with trivial finite part: a small-parameter bound $\|W(x_0)(\mathrm{diag}(a,1)kg)\|\le C_g\prod_{v\mid\infty}\|a_v\|^{\mathrm{mult}(v)w/2}\min(1,\|a_v\|)^{\delta}$ for some $\delta>0$, and a large-parameter bound $\le C_g\,\mathrm{ideleNorm}(a)^{w/2}\|a_v\|^{-M}$ for every $M\in\mathbb N$ and every infinite place $v$, and the same two bounds for $y_1$. Let $g_x,g_y$ have identity archimedean part, $t_x,t_y$ be ideles with trivial finite part, $k_x,k_y$ have identity finite part with all archimedean components row isometries, and suppose $W(x_0)(\mathrm{diag}(t_x,1)k_xg_x)\ne 0$ and $W(y_1)(\mathrm{diag}(t_y,1)k_yg_y)\ne 0$. Then there exist $h$ with identity finite part and a continuous $finf:\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ satisfying `IsArchKFinite` (at each infinite place its right translates under the row-isometry subgroup satisfy `RightTranslatesSpanFinite`), such that $finf(mk)=\nu(m_{11}^{\,\prime})\,finf(k)$ — with $m_{11}^{\,\prime}$ the lower right entry of $m$, a unit by `borelDiagSnd` — whenever $m$ lies in the adelic Borel subgroup (vanishing lower left entry), $m$ and $k$ have identity finite part and all their archimedean components are row isometries, and such that $$\int finf(k)\Big(\int W(x_0)(\mathrm{diag}(t,1)kg_x)\,\overline{W(y_1(\cdot\, h))(\mathrm{diag}(t,1)kg_y)}\,\mathrm{ideleNorm}(t)^{-w}\,d\,\mathrm{sPartMeasure}_\emptyset(t)\Big)\,d\,\mathrm{maximalCompactAtHaar}_\emptyset(k)\ne 0,$$ the outer integral being over the maximal compact subgroup with all finite components trivial, with its Haar measure.
--
--   This is the archimedean half of the non-vanishing of the Rankin–Selberg integral attached to a pair of Whittaker functions, with the Eisenstein datum $finf$ and the aligning archimedean translate $h$ produced last from the given non-vanishing values. It feeds the construction of test data for which the pair of $s$-part integrals is analytic and non-zero near the centre, used in [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_archTranslate_isArchKFinite_equivariant_integral_mul_torusIntegral_whittakerCoefficient_ne_zero.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

theorem AutomorphicForm.RankinSelberg.exists_archTranslate_isArchKFinite_equivariant_integral_mul_torusIntegral_whittakerCoefficient_ne_zero
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ωx ωy ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (_htot : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))

    (x₀ y₁ : AdelicGL2 (𝓞 K) K → ℂ) (_hx₀c : Continuous x₀) (_hy₁c : Continuous y₁)
    (_hx₀G : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x₀ (globalPoints (𝓞 K) K γ * g) = x₀ g)
    (_hy₁G : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y₁ (globalPoints (𝓞 K) K γ * g) = y₁ g)
    (_hx₀Z : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x₀ (centralScalar (𝓞 K) K z * g) = ((ωx z : ℂˣ) : ℂ) * x₀ g)
    (_hy₁Z : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y₁ (centralScalar (𝓞 K) K z * g) = ((ωy z : ℂˣ) : ℂ) * y₁ g) :

    ∀ (_hx₀small : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ))
      (_hx₀large : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))
      (_hy₁small : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y₁ 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ))
      (_hy₁large : ∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y₁ 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ)))

      (gx gy : AdelicGL2 (𝓞 K) K) (_hgx : glArch (𝓞 K) K gx = 1) (_hgy : glArch (𝓞 K) K gy = 1)
      (tx : (AdeleRing (𝓞 K) K)ˣ) (_htx : ((tx : AdeleRing (𝓞 K) K)).2 = 1)
      (kx : AdelicGL2 (𝓞 K) K) (_hkx : glFin (𝓞 K) K kx = 1)
      (_hkxi : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K kx)))
      (_hWx : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne tx * kx * gx) ≠ 0)
      (ty : (AdeleRing (𝓞 K) K)ˣ) (_hty : ((ty : AdeleRing (𝓞 K) K)).2 = 1)
      (ky : AdelicGL2 (𝓞 K) K) (_hky : glFin (𝓞 K) K ky = 1)
      (_hkyi : ∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K ky)))
      (_hWy : whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y₁ 1
          (diagOne ty * ky * gy) ≠ 0),
    ∃ (h : AdelicGL2 (𝓞 K) K) (finf : AdelicGL2 (𝓞 K) K → ℂ),
      glFin (𝓞 K) K h = 1 ∧ Continuous finf ∧ IsArchKFinite K finf ∧
      (∀ (m k : AdelicGL2 (𝓞 K) K) (hm : m ∈ adelicBorel (𝓞 K) K),
        glFin (𝓞 K) K m = 1 → glFin (𝓞 K) K k = 1 →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K m))) →
        (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          finf (m * k) = ((ν (borelDiagSnd (⟨m, hm⟩ : ↥(adelicBorel (𝓞 K) K))) : ℂˣ) : ℂ) * finf k) ∧
      ∫ k, finf (k : AdelicGL2 (𝓞 K) K) *
          (∫ t, whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₀ 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * gx) *
              (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g => y₁ (g * h)) 1
          (diagOne t * (k : AdelicGL2 (𝓞 K) K) * gy)) *
              ((NumberField.TateGlobal.ideleNorm K t ^ (-w) : ℝ) : ℂ) ∂(NumberField.Idele.sPartMeasure K ∅))
        ∂(maximalCompactAtHaar K ∅) ≠ 0 := by sorry
