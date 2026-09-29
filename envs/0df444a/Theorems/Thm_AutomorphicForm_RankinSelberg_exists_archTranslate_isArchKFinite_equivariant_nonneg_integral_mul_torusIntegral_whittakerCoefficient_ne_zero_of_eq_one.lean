-- Prove2me | Theorems.Thm_AutomorphicForm_RankinSelberg_exists_archTranslate_isArchKFinite_equivariant_nonneg_integral_mul_torusIntegral_whittakerCoefficient_ne_zero_of_eq_one
-- name    : AutomorphicForm.RankinSelberg.exists_archTranslate_isArchKFinite_equivariant_nonneg_integral_mul_torusIntegral_whittakerCoefficient_ne_zero_of_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/b50e6a20-361e-58e5-82d4-1a5663dd2738
-- title:
--   Non-vanishing Rankin–Selberg torus pairing against a non-negative K-finite datum
-- statement:
--   Let $K$ be a number field, $D_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and $\omega_x,\omega_y,\nu$ characters of the idele group with values in $\mathbb{C}^\times$, $w$ real, such that $|\omega_x(z)|=|\omega_y(z)|=\lVert z\rVert^{w}$ where $\lVert\cdot\rVert$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), $\nu$ continuous, $\omega_x(z)\overline{\omega_y(z)}\nu(z)=\lVert z\rVert^{2w}$, and $\nu=1$. Let $x_0,y_1:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant under left multiplication by $\mathrm{GL}_2(K)$, and transforming under central scalars $z$ by $\omega_x$ resp. $\omega_y$. Throughout, $W[\varphi](g)$ denotes the Whittaker coefficient at $\alpha=1$ of $\varphi$ for the standard additive character, that is $\int \varphi\big(\binom{1\ x}{0\ 1}g\big)\psi(-x)$ against the adelic additive Haar measure conditioned on the box $\mathrm{adelicBox}\,K$ (fundamental domain at the infinite places times the integral finite adeles), the remaining entries of the `CarrierPins` datum being $D_0$, the levels $N\mapsto \mathrm{levelOne}\sqcap\mathrm{finiteAdelicGL2Subgroup}$ and the Hecke generators `heckeGen`. Assume, for $\varphi=x_0$ and $\varphi=y_1$, the following torus decay, uniformly over the compact directions: for every $g$ with trivial archimedean component there are $\delta>0$ and $C_g$ with $\lVert W[\varphi](\mathrm{diag}(a,1)kg)\rVert\le C_g\prod_{v\mid\infty}\lVert a_v\rVert^{m_v w/2}\min(1,\lVert a_v\rVert)^{\delta}$, and for each $M\in\mathbb{N}$ a constant $C_g$ with $\lVert W[\varphi](\mathrm{diag}(a,1)kg)\rVert\le C_g\lVert a\rVert^{w/2}\lVert a_v\rVert^{-M}$ at every infinite place $v$, both for all $k$ with trivial finite component whose archimedean components are row isometries (norm-one determinant and preservation of $\lVert x\rVert^2+\lVert y\rVert^2$ under the row action) and all ideles $a$ with trivial finite component; here $m_v$ is the multiplicity of $v$. Let finally $g_x,g_y$ have trivial archimedean component, and let $t_x,t_y$ be ideles with trivial finite component and $k_x,k_y$ elements with trivial finite component and row-isometric archimedean components such that $W[x_0](\mathrm{diag}(t_x,1)k_xg_x)\ne 0$ and $W[y_1](\mathrm{diag}(t_y,1)k_yg_y)\ne 0$. Then there exist $h\in\mathrm{GL}_2(\mathbb{A}_K)$ with trivial finite component and a continuous $f_\infty:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is archimedean $K$-finite (`IsArchKFinite`: at each infinite place its right translates under the row-isometry subgroup span finitely), takes values with nonnegative real part and vanishing imaginary part, satisfies $f_\infty(mk)=\nu(b(m))f_\infty(k)$ for all $m$ in the Borel subgroup (lower-left entry zero) and all $k$, both with trivial finite component and row-isometric archimedean components, $b(m)$ being the lower-right diagonal entry of $m$ as a unit, and for which $$\int f_\infty(k)\Big(\int W[x_0](\mathrm{diag}(t,1)kg_x)\,\overline{W[y_1(\,\cdot\,h)](\mathrm{diag}(t,1)kg_y)}\,\lVert t\rVert^{-w}\,d\,\mathrm{sPartMeasure}_{\emptyset}(t)\Big)\,d\,\mathrm{maximalCompactAtHaar}_{\emptyset}(k)\ne 0,$$ the outer integral being over the group $\mathrm{adelicMaximalCompact}\,K$ intersected with the kernels of all finite components, with its Haar measure, and the inner one over the ideles with the pushforward under $\mathrm{partAt}_{\emptyset}$ of idelic Haar measure restricted to the ideles integral at every finite place.
--
--   This is the archimedean half of the non-vanishing of the Rankin–Selberg integral of two Whittaker functions on $\mathrm{GL}(2)$ at the centre, with the Eisenstein datum $f_\infty$ (and an archimedean translate $h$ aligning the two base points) chosen after the two forms. It feeds [`AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero`](thm.html#AutomorphicForm.RankinSelberg.exists_testData_sPartIntegral_pair_analyticOnNhd_ne_zero), where the pairing is assembled into an analytic family of test data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_RankinSelberg_exists_archTranslate_isArchKFinite_equivariant_nonneg_integral_mul_torusIntegral_whittakerCoefficient_ne_zero_of_eq_one.lean

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

theorem AutomorphicForm.RankinSelberg.exists_archTranslate_isArchKFinite_equivariant_nonneg_integral_mul_torusIntegral_whittakerCoefficient_ne_zero_of_eq_one
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ωx ωy ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (_hωx : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωx z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (_hωy : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ωy z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
    (_htot : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ((ωx z : ℂˣ) : ℂ) * (starRingEnd ℂ) ((ωy z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) =
        ((NumberField.TateGlobal.ideleNorm K z ^ (2 * w) : ℝ) : ℂ))
    (_hν1 : ν = 1)

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
      (∀ g : AdelicGL2 (𝓞 K) K, 0 ≤ (finf g).re ∧ (finf g).im = 0) ∧
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
