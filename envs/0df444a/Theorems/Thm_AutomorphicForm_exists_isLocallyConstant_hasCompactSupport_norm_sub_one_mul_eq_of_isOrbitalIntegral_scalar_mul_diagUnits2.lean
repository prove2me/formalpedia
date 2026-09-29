-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6f073bbc-b050-5fab-8695-0d3846476fd0
-- title:
--   Normalised split orbital integrals as a test function on the torus
-- statement:
--   Let $K$ be a number field, $v$ a finite place of $K$ (a height-one prime of $\mathcal{O}_K$), and let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, i.e. locally constant with compact support. Then there exists a single function $\Phi : K_v^\times \times K_v^\times \to \mathbb{C}$ which is locally constant and of compact support and has the following property. Let $u, z \in K_v^\times$ with $u \neq 1$ in $K_v$, and put $\gamma = z \cdot \mathrm{diag}(u,1)$, the product of the scalar matrix with entry $z$ and the diagonal unit matrix `diagUnits2 u 1`. Let $\tau$ be any measure on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, taken with its Borel $\sigma$-algebra, such that $\tau$ is a Haar measure and $\tau$ gives mass $1$ to the set of elements of the centraliser lying in [`AutomorphicForm.localIntegralSet`](def/AutomorphicForm_LocalOrbitalBase.html#L100), the set of $g$ with both $g$ and $g^{-1}$ having entries in the valuation ring of $K_v$. Let $I \in \mathbb{C}$ be any value satisfying [`AutomorphicForm.IsOrbitalIntegral`](def/AutomorphicForm_LocalOrbitalBase.html#L208) for $\gamma$, $\tau$ and $f_v$, that is: there is a non-negative measurable $w : \mathrm{GL}_2(K_v) \to \mathbb{R}$ of compact support with $\int_{Z(\gamma)} w(tx)\,d\tau(t) = 1$ for every $x$ with $f_v(x^{-1}\gamma x) \neq 0$, and $I = \int f_v(x^{-1}\gamma x)\, w(x)$ against the Haar measure [`AutomorphicForm.localHaar`](def/AutomorphicForm_LocalOrbitalBase.html#L168) on $\mathrm{GL}_2(K_v)$. Then $\|u-1\|_v \cdot I = \Phi(u,z)$. In particular the normalised orbital integral at the regular split elements $\gamma$ is independent of the admissible choices of $\tau$ and of the section function $w$.
--
--   This is the non-archimedean local window at a finite place: Harish-Chandra's descent to the split torus, in the form asserting that the orbital integrals of a local test function at the regular split elements $z\cdot\mathrm{diag}(u,1)$, multiplied by $\|u-1\|_v$, are the values of one locally constant compactly supported function of $(u,z)$. It feeds the local–global comparison of orbital integrals used in the trace-formula arguments behind the Langlands–Tunnell step, and is cited by the statements assembling the global class sums and by the variant phrased through the component of an adelic matrix at $v$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_WindingDatum
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      ∀ (u z : (v.adicCompletion K)ˣ), (u : v.adicCompletion K) ≠ 1 →
        ∀ (τ : @Measure (AutomorphicForm.localCentralizer K v
              (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1))),
          @Measure.IsHaarMeasure _ _ _
            (AutomorphicForm.localCentralizerBorel K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1)) τ →
          τ (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1 →
          ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v (Matrix.GeneralLinearGroup.scalar (Fin 2) z * diagUnits2 u 1) τ fv I →
            (‖(u : v.adicCompletion K) - 1‖ : ℂ) * I = Φ (u, z) := by sorry
