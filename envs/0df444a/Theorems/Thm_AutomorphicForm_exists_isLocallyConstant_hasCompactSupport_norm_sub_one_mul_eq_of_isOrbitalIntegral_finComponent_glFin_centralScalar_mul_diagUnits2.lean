-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/979c74da-5ea3-567e-bd87-17749cade6db
-- title:
--   Finite-place window function for a family of orbital integrals
-- statement:
--   Let $K$ be a number field, $v$ a maximal ideal of $\mathcal{O}_K$ with completion $K_v$, and $u \in K^\times$ with $u \neq 1$ in $K$. Let $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be a local test function, i.e. locally constant with compact support. For each $z \in (\mathbb{A}_K)^\times$ write $\gamma(z)$ for the image under `AdelicLevel.glFin` followed by `AdelicLevel.finComponent` at $v$ — that is, the $v$-component of the entrywise map to the finite adeles — of the element $\mathrm{scalar}(z)\cdot\mathrm{diag}(\iota u, 1)$ of $\mathrm{GL}_2(\mathbb{A}_K)$, where $\iota : K^\times \to (\mathbb{A}_K)^\times$ is induced by the structure map and $\mathrm{scalar}$ is the central embedding. Assume given, for each $z$, a measure $\tau_F(z)$ on the centraliser of $\{\gamma(z)\}$ in $\mathrm{GL}_2(K_v)$, taken with its Borel $\sigma$-algebra, which is a Haar measure and which gives mass $1$ to the set of elements of the centraliser whose underlying matrix and inverse matrix both have entries in the valuation ring $\mathcal{O}_v$. Then there is a single locally constant, compactly supported $\Phi : K_v^\times \times K_v^\times \to \mathbb{C}$, depending on neither $z$ nor the chosen measures, such that for every $z$ and every $I \in \mathbb{C}$ which is an orbital-integral value of $f_v$ at $\gamma(z)$ relative to $\tau_F(z)$ — meaning that for some section weight $w$ satisfying [`AutomorphicForm.IsSectionFn`](def/AutomorphicForm_LocalOrbitalBase.html#L200) for these data one has $I = \int_{\mathrm{GL}_2(K_v)} f_v(x^{-1}\gamma(z)x)\,w(x)$ against the local Haar measure — one has $\|u_v - 1\|\cdot I = \Phi(u_v, z_v)$, where $u_v$ is the image of $u$ in $K_v^\times$ and $z_v$ is the $v$-component [`NumberField.AdeleRing.finiteUnitsComponent`](def/NumberField_IdeleBox.html#L106) of $z$.
--
--   This is the finite-place half of the local analysis of orbital integrals along the family of split regular semisimple classes $\mathrm{scalar}(z)\,\mathrm{diag}(u,1)$: all values at all places in the family are captured by one locally constant compactly supported function of the pair $(u_v, z_v)$. It feeds the integrability statements for products of local orbital integrals over the idele class group used in the comparison of trace formulae.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical in

theorem AutomorphicForm.exists_isLocallyConstant_hasCompactSupport_norm_sub_one_mul_eq_of_isOrbitalIntegral_finComponent_glFin_centralScalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u : Kˣ) (hu1 : (u : K) ≠ 1)
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (τF : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      @Measure (AutomorphicForm.localCentralizer K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))))
        (AutomorphicForm.localCentralizerBorel K v
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))))
    (hτF : ∀ z, @Measure.IsHaarMeasure _ _ _
      (AutomorphicForm.localCentralizerBorel K v
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))) (τF z))
    (hτF1 : ∀ z, τF z (Subtype.val ⁻¹' AutomorphicForm.localIntegralSet K v) = 1) :
    ∃ Φ : (v.adicCompletion K)ˣ × (v.adicCompletion K)ˣ → ℂ, IsLocallyConstant Φ ∧ HasCompactSupport Φ ∧
      ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegral K v
            (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) (τF z) fv I →
          (‖algebraMap K (v.adicCompletion K) (u : K) - 1‖ : ℂ) * I =
            Φ (Units.map (algebraMap K (v.adicCompletion K) : K →* v.adicCompletion K) u,
              NumberField.AdeleRing.finiteUnitsComponent (𝓞 K) K v z) := by sorry
