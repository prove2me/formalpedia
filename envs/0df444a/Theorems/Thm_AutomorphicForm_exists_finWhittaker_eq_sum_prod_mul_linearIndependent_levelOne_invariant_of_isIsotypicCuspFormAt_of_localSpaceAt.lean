-- Prove2me | Theorems.Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
-- name    : AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/ecf2a83b-76f3-54c7-9bbb-d1f37f96eca3
-- title:
--   Independent tensor splitting of the finite Whittaker factor
-- statement:
--   Fix a Hecke eigensystem $\Phi$ over $\mathbb{Q}$ with complex coefficients (a nonzero level ideal of $\mathcal{O}_{\mathbb{Q}}$ together with coefficient functions $a,b$ on finite places), a finite set $SQ$ of height-one primes containing every prime $p$ with $\Phi.\mathrm{level} \le p$, a further finite set $S$, and a smooth cusp realisation $R$ at `productionPinsGeneral` for the twisted eigensystem `Φ.toRawCentral` (whose $b$-coefficients are $\Phi.b$ divided by the absolute norm), used only through its central character `R.centralChar`. Let $\varphi_{\mathrm{par}}$, indexed by parity vectors $(\mathrm{InfinitePlace}\,\mathbb{Q} \to \mathbb{Z}/2)$, be functions on $\mathrm{GL}_2$ of the adeles which are each `IsIsotypicCuspFormAt` for those pins, this central character, level $\Phi.\mathrm{level}$, exceptional set $S$ and $\Phi$ (smooth cuspidal automorphic, continuous, right invariant under the level-one group of $\Phi.\mathrm{level}$ intersected with the finite-adelic subgroup, Hecke eigenfunction with eigenvalue $\Phi.a(v)$ and central eigenvalue $(\mathrm{N}v)^{-1}\Phi.b(v)$ outside $S$) and each nonzero. Assume the $\psi_{\mathbb{Q}}$-Whittaker coefficient at $1$ of $\varphi_{\mathrm{par}}$ factorises as $W_A^{\mathrm{par}}(g_\infty)\,W_f^{\mathrm{par}}(g_{\mathrm{fin}})$ for all $g$, with $g_\infty$, $g_{\mathrm{fin}}$ the real and finite factors of $g$. Fix a parity $\mathrm{par}$ and assume, for each $p \in SQ$, that the local Whittaker space `localSpaceAt` at $p$ of $\varphi_{\mathrm{par}}$ is irreducible (each nonzero element generates it under right translation), admissible (the $U$-fixed vectors lie in the span of a finite set, for every open subgroup $U$) and smooth (every element is right invariant under some open subgroup). Then there are $m \in \mathbb{N}$, slot functions $w_{p,\alpha}$ on $\mathrm{GL}_2(\mathbb{Q}_p)$ for $p \in SQ$, $\alpha \in \mathrm{Fin}\,m$, and remainders $W'_\alpha$ on adelic $\mathrm{GL}_2$, such that: each $w_{p,\alpha}$ lies in the local Whittaker space at $p$; each $W'_\alpha$ is right invariant under the image of $\mathrm{GL}_2(\mathbb{Q}_p)$ for $p \in SQ$; $w_{p,\alpha}(u(x)g) = \psi_p(x)\,w_{p,\alpha}(g)$; $W'_\alpha(u(t)g) = \psi_{\mathbb{Q}}(t)\,W'_\alpha(g)$ for adeles $t$ with zero archimedean component and trivial unipotent image at each $p \in SQ$; the $w_{p,\alpha}$ and $W'_\alpha$ are measurable on the finite-adelic subgroup; each $w_{p,\alpha}$ is right invariant under some open subgroup and under the local level-one group of $\Phi.\mathrm{level}$ at $p$; each $W'_\alpha$ is right invariant under every finite-adelic $k$ which is integral (in the local level-one group of the unit ideal) outside $SQ$ and trivial at $SQ$; the tensors $y \mapsto \prod_{p \in SQ} w_{p,\alpha}(y_p)$ are linearly independent over $\mathbb{C}$; and $W_f^{\mathrm{par}}(g_{\mathrm{fin}}) = \sum_{\alpha} \bigl(\prod_{p \in SQ} w_{p,\alpha}(g_p)\bigr) W'_\alpha(g)$ for all $g$.
--
--   This is the Flath-style simultaneous tensor factorisation of the finite Whittaker factor at the finitely many primes of $SQ$, strengthened so that the slot tensors form a linearly independent family and the remainders inherit right invariance under the integral subgroup away from $SQ$. It feeds the Rankin–Selberg integral analysis in the converse-theorem part of the Langlands–Tunnell input, where a non-vanishing finite integral is extracted from such a splitting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt.lean

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

theorem AutomorphicForm.exists_finWhittaker_eq_sum_prod_mul_linearIndependent_levelOne_invariant_of_isIsotypicCuspFormAt_of_localSpaceAt
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))

    (hSQ1 : ∀ p : HeightOneSpectrum (𝓞 ℚ), Φ.level ≤ p.asIdeal → p ∈ SQ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (R : SmoothCuspRealizationAt ℚ (productionPinsGeneral ℚ) Φ.toRawCentral)
    (φv : (InfinitePlace ℚ → ZMod 2) → AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (hiso : ∀ par, IsIsotypicCuspFormAt ℚ (productionPinsGeneral ℚ) R.centralChar Φ.level S Φ (φv par))
    (hφne : ∀ par, φv par ≠ 0)
    (WA : (InfinitePlace ℚ → ZMod 2) → GL (Fin 2) ℝ → ℂ)
    (Wf : (InfinitePlace ℚ → ZMod 2) → finiteAdelicGL2Subgroup ℚ → ℂ)
    (hWAf : ∀ par (g : AdelicGL2 (𝓞 ℚ) ℚ),
      whittakerCoefficient ℚ (productionPinsOf ℚ (classRepSiegelSet ℚ (1 / 2) 1 (1 / 2) 2) (fun N => levelOne (𝓞 ℚ) ℚ N ⊓ finiteAdelicGL2Subgroup ℚ) (fun v => heckeGen (𝓞 ℚ) ℚ v) (adelicBox ℚ)) NumberField.StandardAddChar.psiQ (φv par) 1 g = WA par (ratArchGL2 g) * Wf par (RSCarrier.finFactor g))
    (par : InfinitePlace ℚ → ZMod 2)

    (hV : ∀ p ∈ SQ,
      ((∀ W₀ ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          W₀ ≠ 0 → ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            W ∈ Submodule.span ℂ (Set.range fun h : GL (Fin 2) (p.adicCompletion ℚ) => fun g : GL (Fin 2) (p.adicCompletion ℚ) => W₀ (g * h))) ∧
        (∀ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) →
          ∃ B : Finset (GL (Fin 2) (p.adicCompletion ℚ) → ℂ), ∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
            (∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g) → W ∈ Submodule.span ℂ (B : Set (GL (Fin 2) (p.adicCompletion ℚ) → ℂ))) ∧
        (∀ W ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ p (φv par),
          ∃ U : Subgroup (GL (Fin 2) (p.adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) (p.adicCompletion ℚ))) ∧ ∀ k ∈ U, ∀ g : GL (Fin 2) (p.adicCompletion ℚ), W (g * k) = W g))) :
    ∃ (m : ℕ) (w : ∀ p : ↥SQ, Fin m → GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) → ℂ)
      (W' : Fin m → AdelicGL2 (𝓞 ℚ) ℚ → ℂ),

      (∀ (p : ↥SQ) (α : Fin m),
        w p α ∈ AutomorphicForm.WhittakerModel.localSpaceAt ℚ (productionPinsGeneral ℚ) NumberField.StandardAddChar.psiQ (p : HeightOneSpectrum (𝓞 ℚ)) (φv par)) ∧

      (∀ (α : Fin m) (p : ↥SQ) (x : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
        W' α (g * UnramifiedWhittaker.placeEmbed ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x) = W' α g) ∧

      (∀ (p : ↥SQ) (α : Fin m) (x : (p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ) (g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)),
        w p α (UnramifiedWhittaker.unipotent x * g) = NumberField.StandardAddChar.psiLocal ℚ (p : HeightOneSpectrum (𝓞 ℚ)) x * w p α g) ∧

      (∀ (α : Fin m) (t : AdeleRing (𝓞 ℚ) ℚ), t.1 = 0 → (∀ p : ↥SQ, localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (unipotentGL2 t) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (unipotentGL2 t * g) = NumberField.StandardAddChar.psiQ t * W' α g) ∧

      (∀ (p : ↥SQ) (α : Fin m),
        Measurable (fun g : finiteAdelicGL2Subgroup ℚ => w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ)))) ∧
      (∀ α : Fin m, Measurable (fun g : finiteAdelicGL2Subgroup ℚ => W' α (g : AdelicGL2 (𝓞 ℚ) ℚ))) ∧

      (∀ (p : ↥SQ) (α : Fin m), ∃ U : Subgroup (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ)), IsOpen (U : Set (GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ))) ∧
        ∀ k ∈ U, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (p : ↥SQ) (α : Fin m), ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ (p : HeightOneSpectrum (𝓞 ℚ)) Φ.level, ∀ g : GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ), w p α (g * k) = w p α g) ∧

      (∀ (α : Fin m) (k : finiteAdelicGL2Subgroup ℚ),
        (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
          localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
        (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
        ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' α (g * (k : AdelicGL2 (𝓞 ℚ) ℚ)) = W' α g) ∧

      (∀ c : Fin m → ℂ,
        (∀ y : ∀ p : ↥SQ, GL (Fin 2) ((p : HeightOneSpectrum (𝓞 ℚ)).adicCompletion ℚ),
          ∑ α : Fin m, c α * ∏ p : ↥SQ, w p α (y p) = 0) → ∀ α : Fin m, c α = 0) ∧

      ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
        Wf par (RSCarrier.finFactor g) = ∑ α : Fin m, (∏ p : ↥SQ, w p α (localAt ℚ (p : HeightOneSpectrum (𝓞 ℚ)) g)) * W' α g := by sorry
