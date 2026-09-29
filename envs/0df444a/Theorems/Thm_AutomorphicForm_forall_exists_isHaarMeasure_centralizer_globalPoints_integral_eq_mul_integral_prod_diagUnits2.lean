-- Prove2me | Theorems.Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
-- name    : AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d0e17935-ca7e-55b5-a734-b8da1a3b5ff4
-- title:
--   Haar measure on centralisers of regular diagonal elements
-- statement:
--   Let $K$ be a number field, and equip the idele class group's unit group $(\mathbb{A}_K)^\times = (\mathrm{AdeleRing}(\mathcal{O}_K,K))^\times$ with a measurable space structure that is the Borel structure of its topology, let $\nu_{Z,K}$ be a Haar measure on $(\mathbb{A}_K)^\times$, and let $c_{\tau,K}$ be a real number with $0 < c_{\tau,K}$. Throughout, $\mathrm{GL}_2(\mathbb{A}_K)$ and the centraliser subgroups inside it carry their Borel $\sigma$-algebras, via `glBorel` and `centralizerBorel`. The assertion is that for every $\gamma \in \mathrm{GL}_2(K)$ whose underlying matrix satisfies $\gamma_{10} = 0$, $\gamma_{01} = 0$ and $\gamma_{00}/\gamma_{11} \neq 1$, there exists a measure $\tau$ on the centraliser in $\mathrm{GL}_2(\mathbb{A}_K)$ of the singleton consisting of the image of $\gamma$ under `globalPoints`, the map $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$ induced entrywise by $K \to \mathbb{A}_K$, such that $\tau$ is a Haar measure and such that for every function $g : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$,
--   $$\int_{s} g(s)\,\mathrm{d}\tau = c_{\tau,K} \int g(\mathrm{diag}(p_1,p_2))\,\mathrm{d}(\nu_{Z,K} \otimes \nu_{Z,K})(p),$$
--   the left integral being over the centraliser (with $s$ mapped into $\mathrm{GL}_2(\mathbb{A}_K)$) and the right one over pairs of ideles, where $\mathrm{diag}(p_1,p_2)$ is `diagUnits2 p.1 p.2`, the invertible diagonal matrix with entries $p_1, p_2$. No measurability or integrability hypothesis is imposed on $g$: the equality is claimed for all $g$, with the Bochner integral taken in Mathlib's convention.
--
--   This provides, for each regular split diagonal rational class, a Haar measure on its adelic centraliser — the full diagonal torus, identified with $(\mathbb{A}_K)^\times \times (\mathbb{A}_K)^\times$ — normalised so that the transport of $\nu_{Z,K} \otimes \nu_{Z,K}$ along $\mathrm{diag}$ is scaled by an arbitrary prescribed positive constant. It is the source of the torus measures used in the hyperbolic terms of the comparison of automorphic trace expansions, and is cited by the statements producing those hyperbolic contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_TwistedGeometricRemainder
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.forall_exists_isHaarMeasure_centralizer_globalPoints_integral_eq_mul_integral_prod_diagUnits2
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (cτK : ℝ) (hcτK : 0 < cτK) :
    ∀ γ : GL (Fin 2) K, (γ : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 → (γ : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 →
      (γ : Matrix (Fin 2) (Fin 2) K) 0 0 / (γ : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 1 →
    ∃ τ : Measure (Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K))),
      τ.IsHaarMeasure ∧
      ∀ g : AdelicGL2 (𝓞 K) K → ℂ,
        ∫ s : Subgroup.centralizer ({AutomorphicForm.globalPoints (𝓞 K) K γ} : Set (AdelicGL2 (𝓞 K) K)),
            g (s : AdelicGL2 (𝓞 K) K) ∂τ =
          cτK * ∫ p : (AdeleRing (𝓞 K) K)ˣ × (AdeleRing (𝓞 K) K)ˣ, g (diagUnits2 p.1 p.2) ∂(νZK.prod νZK) := by sorry
