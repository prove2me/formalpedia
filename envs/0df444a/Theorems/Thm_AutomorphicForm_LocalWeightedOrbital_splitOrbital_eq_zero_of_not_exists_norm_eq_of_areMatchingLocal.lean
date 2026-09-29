-- Prove2me | Theorems.Thm_AutomorphicForm_LocalWeightedOrbital_splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal
-- name    : AutomorphicForm.LocalWeightedOrbital.splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/492585ac-b177-5571-ae65-e72d64206dad
-- title:
--   Split orbital vanishing at a non-norm parameter
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ finite Galois, let $\sigma$ be an automorphism of $L$ over $K$ whose integral powers exhaust $\mathrm{Gal}(L/K)$, and assume $[L:K]$ is prime. Let $v$ be a height one prime of $\mathcal{O}_K$, with completion $K_v$. Let $\varphi : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be a semi-local test function, i.e. locally constant with compact support, and let $f : \mathrm{GL}_2(K_v) \to \mathbb{C}$ be likewise locally constant with compact support; assume $\varphi$ and $f$ match in the sense of [`AutomorphicForm.AreMatchingOn`](def/AutomorphicForm_TwistedOrbital.html#L324) for $\sigma$ with respect to the Haar measures `semiLocalHaar` on $\mathrm{GL}_2(L \otimes_K K_v)$ and `localHaar` on $\mathrm{GL}_2(K_v)$. Let $\mu$ be any additive Haar measure on $K_v$, taken with its Borel structure. The conclusion, for the Borel $\sigma$-algebra on $\mathrm{GL}_2(K_v)$, is: for every $a \in K_v^{\times}$ for which no unit $\alpha$ of $L \otimes_K K_v$ satisfies $\mathrm{N}_{(L \otimes_K K_v)/K_v}(\alpha) = a$, and every $t \in K_v^\times$ with $t \neq 1$, the split orbital integral $\int_{K_v} \int f(\mathtt{arg}\, k\, a\, (at)\, x)\, d k\, d\mu(x)$ vanishes, the inner integral being over `localHaar` restricted to the set of $g \in \mathrm{GL}_2(K_v)$ with both $g$ and $g^{-1}$ having entries in the valuation ring $\mathcal{O}_v$.
--
--   This is the local vanishing statement for the split (regular semisimple, non-elliptic) parameters $\mathrm{diag}(a, at)$, $t \neq 1$, whose determinant-type invariant $a$ fails to be a norm from $(L \otimes_K K_v)^\times$: for such parameters no twisted conjugacy class matches, so the matching condition on the pair $(\varphi, f)$ forces the corresponding orbital integrals of $f$ to vanish. It feeds the estimate [`AutomorphicForm.exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal`](thm.html#AutomorphicForm.exists_forall_norm_halfWeighted_sub_le_of_not_exists_norm_eq_of_areMatchingLocal) in the local analysis of base change for $\mathrm{GL}_2$ along the cyclic prime-degree extension $L/K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_LocalWeightedOrbital_splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_LocalWeightedOrbital
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
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel
  AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions in
open scoped Classical in

theorem AutomorphicForm.LocalWeightedOrbital.splitOrbital_eq_zero_of_not_exists_norm_eq_of_areMatchingLocal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    (v : HeightOneSpectrum (𝓞 K))
    (φ : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφ : AutomorphicForm.IsSemiLocalTestFn K L v φ)
    (f : GL (Fin 2) (v.adicCompletion K) → ℂ) (hf : AutomorphicForm.IsLocalTestFn K v f)
    (hmatch : AutomorphicForm.AreMatchingLocal K L v σ φ f)
    [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] :
    letI := AutomorphicForm.localGLBorel K v
    ∀ a : (v.adicCompletion K)ˣ, (¬ ∃ α : (L ⊗[K] (v.adicCompletion K))ˣ, Algebra.norm (v.adicCompletion K) (α : (L ⊗[K] (v.adicCompletion K))) = (a : (v.adicCompletion K))) →
      ∀ t : (v.adicCompletion K)ˣ, t ≠ 1 →
        AutomorphicForm.LocalWeightedOrbital.splitOrbital
          ((AutomorphicForm.localHaar K v).restrict (AutomorphicForm.localIntegralSet K v)) μ f a (a * t) = 0 := by sorry
