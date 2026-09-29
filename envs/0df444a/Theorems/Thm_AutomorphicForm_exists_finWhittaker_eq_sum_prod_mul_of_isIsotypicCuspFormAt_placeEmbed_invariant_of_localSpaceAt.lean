-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
-- name    : AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/342213aa-d45e-51fd-8a95-6ee87c5f5563
-- title:
--   Simultaneous splitting of the finite Whittaker factor over T
-- statement:
--   Let $\Phi$ be a Hecke eigensystem over $\mathbb Q$ with complex coefficients (a nonzero level ideal and eigenvalue families $a,b$), let $S$ be a finite set of primes of $\mathcal O_{\mathbb Q}$, and let $R$ be a smooth cuspidal realisation at the pins `productionPinsGeneral ℚ` of the eigensystem `Φ.toRawCentral` obtained from $\Phi$ by replacing $b_v$ with $(\operatorname{N}v)^{-1}b_v$. Let $\varphi_{\mathrm{par}}$, indexed by maps $\mathrm{InfinitePlace}(\mathbb Q)\to\mathbb Z/2$, be functions on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$, each nonzero and each an isotypic cusp form at those pins for the central character `R.centralChar`, the level `Φ.level`, the exceptional set $S$ and $\Phi$ (smooth cuspidal automorphic, continuous, right invariant under $K_1(\text{level})$ intersected with the finite-adelic subgroup, Hecke coset eigenfunction with eigenvalue $a_v$ and central eigenfunction with eigenvalue $(\operatorname{N}v)^{-1}b_v$ outside $S$). Assume that for every parity the Whittaker coefficient at $\alpha=1$ of $\varphi_{\mathrm{par}}$ against `psiQ` factors as $W_A(\mathrm{par})(g_\infty)\cdot W_f(\mathrm{par})(g_f)$, where $g_\infty$ is the real $\mathrm{GL}_2$-component of $g$ and $g_f=(g_\infty)^{-1}g$ its finite factor. Fix a parity $\mathrm{par}$ and a finite set $T$ of primes such that at each $p\in T$ the local Whittaker space $V_p=$ `localSpaceAt ℚ (productionPinsGeneral ℚ) psiQ p (φv par)` (the $\mathbb C$-span of the functions $g\mapsto$ Whittaker coefficient at $1$ of $x\mapsto\varphi_{\mathrm{par}}(xh)$ evaluated at the image of $g$ under the embedding at $p$) satisfies: every nonzero $W_0\in V_p$ generates $V_p$ by right translates; for every open subgroup $U$ of $\mathrm{GL}_2(\mathbb Q_p)$ there is a finite set of functions whose span contains all right $U$-invariant members of $V_p$; and every member of $V_p$ is right invariant under some open subgroup. Then there exist $m\in\mathbb N$, functions $w_{p,\alpha}$ on $\mathrm{GL}_2(\mathbb Q_p)$ for $p\in T$, $\alpha\in\mathrm{Fin}\,m$, and functions $W'_\alpha$ on $\mathrm{GL}_2(\mathbb A_{\mathbb Q})$ such that: each $w_{p,\alpha}\in V_p$; each $W'_\alpha$ is invariant under right multiplication by the image of $\mathrm{GL}_2(\mathbb Q_p)$ under [`UnramifiedWhittaker.placeEmbed`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) for every $p\in T$; $w_{p,\alpha}(n(x)g)=\psi_p(x)\,w_{p,\alpha}(g)$ for $x\in\mathbb Q_p$, with $\psi_p=$ `psiLocal`; $W'_\alpha(n(t)g)=\psi_{\mathbb Q}(t)\,W'_\alpha(g)$ for every adele $t$ with vanishing archimedean part whose unipotent has trivial image at every $p\in T$; the maps $g\mapsto w_{p,\alpha}(g_p)$ and $g\mapsto W'_\alpha(g)$ are measurable on the finite-adelic subgroup; each $w_{p,\alpha}$ is right invariant under some open subgroup and under the local level-one subgroup [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $p$ of level `Φ.level`; for each $p\in T$ every nonzero element $v$ of the span of all right translates of the $w_{p,\alpha}$ has the property that each $w_{p,\alpha}$ lies in the span of the right translates of $v$; and finally, for all $g$, $$W_f(\mathrm{par})(g_f)=\sum_{\alpha}\Big(\prod_{p\in T}w_{p,\alpha}(g_p)\Big)\,W'_\alpha(g).$$
--
--   This is the local–global factorisation of a Whittaker function in the style of Flath's tensor-product decomposition, carried out simultaneously at the finitely many primes of $T$ and in a form that records, slot by slot, the local Whittaker transformation law, the level-one and open-subgroup invariance, measurability and the generation property of the right-translation span. It is the input to the finite-adelic Rankin–Selberg computations in the converse direction of Langlands–Tunnell, where the integral is unfolded one prime of $T$ at a time on the same term, and to a refinement in which the slot functions are in addition linearly independent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_WhittakerModelLocal
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSGlobalIntegral
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Definitions.Def_LanglandsTunnell_HonestLDatum
import Definitions.Def_AutomorphicForm_SmoothingKernel
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_AutomorphyDatum31
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCoordinates
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_DeltaLift

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_of_isIsotypicCuspFormAt_placeEmbed_invariant_of_localSpaceAt
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (par : InfinitePlace ℚ → ZMod 2) (T : Finset (HeightOneSpectrum (𝓞 ℚ)))

    (hV : ∀ p ∈ T,
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) :
    ∃ (m : ℕ) (w : ∀ p : ↥T, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
      (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ),

      (∀ (p : ↥T) (α : Fin m),
        w p α ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (p : HeightOneSpectrum (𝓞 ℚ)) (φv par)) ∧

      (∀ (α : Fin m) (p : ↥T) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W' α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g) ∧

      (∀ (p : ↥T) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g) ∧

      (∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ p : ↥T, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g) ∧

      (∀ (p : ↥T) (α : Fin m),
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
      (∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧

      (∀ (p : ↥T) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (p : ↥T), ∀ v ∈ Submodule.span ℂ (Set.range fun q : Fin m × GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => fun g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => w p q.1 (g * q.2)),
        v ≠ 0 → ∀ α : Fin m,
          w p α ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => fun g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) => v (g * h))) ∧

      (∀ (p : ↥T) (α : Fin m), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Φ.level, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥T, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g := by sorry
