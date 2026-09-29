-- Prove2me | Theorems.Thm_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
-- name    : AutomorphicForm.exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/da0204a6-a6ff-574a-823d-859bf98981ca
-- title:
--   A regular norm pair on a prescribed valuation shell
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, and assume the degree $\operatorname{finrank}_K L$ is a prime number. Let $\sigma$ be a $K$-algebra automorphism of $L$ with $\sigma \neq 1$, let $v$ be a height one prime of $\mathcal{O}_K$, and assume that every height one prime $w'$ of $\mathcal{O}_L$ lying under $v$ (i.e. with $w'$ contracting to $v$) has $\mathrm{ramificationIdx}'$ of $v$ in $w'$ equal to $1$. Let $w$ be a prime of $\mathcal{O}_L$ above $v$, i.e. an element of $v.\mathrm{Extension}\,(\mathcal{O}_L)$, the subtype of height one primes of $\mathcal{O}_L$ contracting to $v$; let $\varpi_K$ be an irreducible element of the valuation ring of the completion $K_v$; and let $e_1, e_2$ be natural numbers. Then there exist units $a, b$ of $K_v$ and units $\alpha, \beta$ of $L \otimes_K K_v$ such that $a \neq b$, such that the norm string of the diagonal matrix $\mathrm{diag}(\alpha,\beta) \in \mathrm{GL}_2(L \otimes_K K_v)$ — the product $\prod_{i=0}^{[L:K]-1}$ of the $i$-fold iterates of the automorphism of $\mathrm{GL}_2(L \otimes_K K_v)$ induced by $\sigma$ acting on the left tensor factor, applied to that matrix — equals the image of $\mathrm{diag}(a,b) \in \mathrm{GL}_2(K_v)$ under the map induced by $x \mapsto 1 \otimes x$, and such that $\|a\| = \|\varpi_K\|^{f e_1}$ and $\|b\| = \|\varpi_K\|^{f e_2}$, where $f$ is $\mathrm{inertiaDeg}'$ of $v$ in the prime underlying $w$.
--
--   This is the local statement that, at a place unramified in a cyclic extension of prime degree, the twisted norm map on diagonal tori hits prescribed valuation shells, with the two diagonal entries distinct (a regular, split norm pair). It is used in the construction of a Hecke word whose twisted orbital integral is matched with an orbital integral on $\mathrm{GL}_2(K_v)$ in the cyclic base change comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LocalLanglands_HeckeCosetSystem
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_SatakeCombinationCoeff
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm
open scoped TensorProduct

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_ne_and_normString_diagUnits2_eq_toTensorGL_and_norm_eq_pow_inertiaDeg_mul_of_ramificationIdx_eq_one_of_prime
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (hdeg : (Module.finrank K L).Prime)
    (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ w' : HeightOneSpectrum (𝓞 L), HeightOneSpectrum.under (𝓞 K) w' = v →
      Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w').asIdeal w'.asIdeal = 1)
    (w : v.Extension (𝓞 L))
    (ϖK : v.adicCompletionIntegers K) (hϖK : Irreducible ϖK)
    (e₁ e₂ : ℕ) :
    ∃ (a b : (v.adicCompletion K)ˣ) (α β : (L ⊗[K] v.adicCompletion K)ˣ),
      a ≠ b ∧
      normString K L (v.adicCompletion K) σ (diagUnits2 α β) = toTensorGL K L (v.adicCompletion K) (diagUnits2 a b) ∧
      ‖((a : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₁) ∧
      ‖((b : (v.adicCompletion K)ˣ) : v.adicCompletion K)‖ =
        ‖((ϖK : v.adicCompletionIntegers K) : v.adicCompletion K)‖ ^ (v.asIdeal.inertiaDeg' w.1.asIdeal * e₂) := by sorry
