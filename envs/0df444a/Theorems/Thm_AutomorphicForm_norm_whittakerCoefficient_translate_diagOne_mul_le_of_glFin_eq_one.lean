-- Prove2me | Theorems.Thm_AutomorphicForm_norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
-- name    : AutomorphicForm.norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/dda304de-36a2-5582-858f-50b617c8bf62
-- title:
--   Uniform torus bounds on Whittaker coefficients pass to archimedean translates
-- statement:
--   Let $K$ be a number field, $D_0$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, $\omega:\mathbb{A}_K^\times\to\mathbb{C}^\times$ a group homomorphism and $w\in\mathbb{R}$ with $|\omega(z)|=\|z\|^{w}$, where $\|\cdot\|$ is the idele norm given by the Haar modulus [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19). Let $x:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ satisfy $x(\mathrm{unipotentGL2}(\beta+u)g)=x(\mathrm{unipotentGL2}(u)g)$ for all $\beta\in K$, $u\in\mathbb{A}_K$, $g$, and $x(zg)=\omega(z)x(g)$ for central scalars $z$. Write $W$ for `whittakerCoefficient` at $\alpha=1$ with the standard additive character and the pins `productionPinsOf` built from $D_0$, the levels $N\mapsto \mathrm{levelOne}\,N\sqcap\ker(\mathrm{glArch})$, the Hecke generators `heckeGen` and the box `adelicBox` (so the inner integral is against additive Haar measure conditioned on that box). Two hypotheses are assumed: for each $g$ with trivial archimedean part there are $\delta>0$ and $C_g$ with $\|W(x)(\mathrm{diag}(a,1)kg)\|\le C_g\prod_{v\mid\infty}\|a_v\|^{\mathrm{mult}(v)w/2}\min(1,\|a_v\|)^{\delta}$, and for each such $g$ and each $M\in\mathbb{N}$ there is $C_g$ with $\|W(x)(\mathrm{diag}(a,1)kg)\|\le C_g\|a\|^{w/2}\|a_v\|^{-M}$ at every infinite place $v$; both range over all $k$ with trivial finite part whose archimedean components are row isometries (unit determinant norm and preservation of $\|x\|^2+\|y\|^2$ under right multiplication) and all ideles $a$ with trivial finite part. Then for every $h$ with trivial finite part, the right translate $g'\mapsto x(g'h)$ satisfies both families of bounds, with possibly different $\delta$ and constants.
--
--   This is the statement that the uniform-in-$K_\infty$ moderate growth and rapid decay estimates for a Whittaker function along the diagonal torus are stable under right translation by an element with trivial finite part, the transfer being effected by an archimedean Iwasawa decomposition together with the unipotent and central transformation laws. It is used in the Rankin–Selberg part of the development, where nonvanishing of integrals pairing translates of such Whittaker coefficients with torus integrals is established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain

theorem AutomorphicForm.norm_whittakerCoefficient_translate_diagOne_mul_le_of_glFin_eq_one
    (K : Type) [Field K] [NumberField K]
    (D₀ : Set (AdelicGL2 (𝓞 K) K))
    (ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (w : ℝ)
    (_hω : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ω z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w)
    (x : AdelicGL2 (𝓞 K) K → ℂ)
    (_hper : ∀ (β : K) (u : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K),
      x (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + u) * g) = x (unipotentGL2 u * g))
    (_hZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ω z : ℂˣ) : ℂ) * x g)
    (_hsmall : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)))
    (_hlarge : (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))))
    (h : AdelicGL2 (𝓞 K) K) (_hh : glFin (𝓞 K) K h = 1) :
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 →
        ∃ δ : ℝ, 0 < δ ∧ ∃ Cg : ℝ,
          ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
            (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
            ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
              ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
                Cg * ∏ pl : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ ((pl.mult : ℝ) * w / 2) *
                  (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 pl‖) ^ δ)) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, glArch (𝓞 K) K g = 1 → ∀ M : ℕ,
        ∃ Cg : ℝ, ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k = 1 →
          (∀ pl : InfinitePlace K, IsRowIsometry (archComponent K pl (glArch (𝓞 K) K k))) →
          ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 → ∀ pl : InfinitePlace K,
            ‖whittakerCoefficient K (productionPinsOf K D₀ (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
          (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) (fun g' => x (g' * h)) 1
          (diagOne a * k * g)‖ ≤
              Cg * NumberField.TateGlobal.ideleNorm K a ^ (w / 2) * ‖((a : AdeleRing (𝓞 K) K)).1 pl‖ ^ (-(M : ℝ))) := by sorry
