-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles
-- name    : AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/f5a8e30e-d764-564d-b939-71b427347a1c
-- title:
--   Polynomial counting bound for archimedean parameters of idele class characters
-- statement:
--   Let $K$ be a number field, $SK$ a finite set of finite places of $K$ (prime ideals of $\mathcal O_K$), $M_0$ and $n_\rho$ natural numbers, and let $\rho_1,\dots,\rho_{n_\rho}$ (indexed by `Fin nρ`) be families assigning to each finite place $v$ a homomorphism $(K_v)^\times \to \mathbb C^\times$. Then there exists $C \ge 0$, depending only on these data, with the following property. Let $\iota E$ be any index type, $\mu : \iota E \to ((\mathbb A_K)^\times \to \mathbb C^\times)$ a family of group homomorphisms such that each $\mu_e$ is unitary ($\|\mu_e(x)\| = 1$ for all ideles $x$), is an idele class character (trivial on the image of $K^\times$), and is continuous as a $\mathbb C$-valued function; let $nE : \iota E \to \mathbb N$ (call $e$ charged when $nE(e) > 0$). Assume: any two distinct charged indices $e \ne e'$ are separated by some $z$ in the norm-one ideles, i.e. in the kernel of the module character `distribHaarChar`, with $\mu_e(z) \ne \mu_{e'}(z)$; there are reals $\tau_{e,v}$ ($v$ archimedean) such that, for every unit $x$ of $K_v$ whose image under the embedding of $K_v$ into $\mathbb C$ is real and positive, the $v$-component $\mu_e \circ \mathrm{archUnitHom}_v$ takes the value $\|x\|^{i\tau_{e,v}}$, the norm being the idele norm of the idele with $x$ at $v$ and $1$ elsewhere; there are integers $m_{e,v}$ such that on units $x$ with $|x|_v = 1$ the same local character is $x \mapsto x^{m_{e,v}}$; for charged $e$ one has $|m_{e,v}| \le M_0$ for all archimedean $v$; and for charged $e$ the character $\mu_e$ is unramified at every finite $v \notin SK$ (its local character is trivial on units $u$ with $u$ and $u^{-1}$ integral), while for some index $r$ its local characters at the places $v \in SK$ agree with $\rho_r$ on all such integral units. Then for every $R \ge 0$ the set of charged $e$ whose parameter vector has spread $\sum_{v,v'} |\tau_{e,v} - \tau_{e,v'}| \le R$ is finite, and its cardinality is at most $C(1+R)^{r-1}$, where $r$ is the number of archimedean places of $K$ (the exponent being truncated natural subtraction).
--
--   This is a sparsity, or counting, statement for the archimedean parameters of a family of continuous unitary Hecke characters of $K$ with prescribed ramification data: within a fixed ramification type the admissible parameter vectors form a lattice-like set, so those of bounded spread number $O((1+R)^{r-1})$. It is the arithmetic input to the convergence and summability estimates for adelic $L$-series, being cited by [`AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne`](thm.html#AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne) and by [`NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq`](thm.html#NumberField.TateGlobal.exists_finite_forall_exists_isUnramifiedCharAt_mul_mul_pow_two_mem_abs_archParam_le_of_localChar_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_forall_finite_and_ncard_archParam_spread_le_of_isUnitaryChar_of_pairwise_ne_normOneIdeles
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (M₀ : ℕ) (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ιE : Type)
      (μ : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (nE : ιE → ℕ)
      (_hdist : ∀ e e' : ιE, e ≠ e' → 0 < nE e → 0 < nE e' →
        ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ μ e' z)
      (τμ : ιE → InfinitePlace K → ℝ)
      (_hτ : ∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I))
      (mμ : ιE → InfinitePlace K → ℤ)
      (_hm : ∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v))
      (_hM₀ : ∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ))
      (_hram : ∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e) v) ∧
        ∃ r : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e) v u = ρs r v u),
      ∀ R : ℝ, 0 ≤ R →
        {e : ιE | 0 < nE e ∧ ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |τμ e v - τμ e v'| ≤ R}.Finite ∧
        (({e : ιE | 0 < nE e ∧ ∑ v : InfinitePlace K, ∑ v' : InfinitePlace K, |τμ e v - τμ e v'| ≤ R}.ncard : ℕ) : ℝ) ≤
          C * (1 + R) ^ (Fintype.card (InfinitePlace K) - 1) := by sorry
