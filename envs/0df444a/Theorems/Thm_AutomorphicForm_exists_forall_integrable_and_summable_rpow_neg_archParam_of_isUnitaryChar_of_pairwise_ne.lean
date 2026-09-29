-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne
-- name    : AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/2d17e4e3-f43a-5452-9bec-4c18b3d5bcbd
-- title:
--   Summability of archimedean parameters at fixed level and type
-- statement:
--   Let $K$ be a number field, $SK$ a finite set of finite places of $K$ (height-one primes of $\mathcal O_K$), $\xi K$ a homomorphism from the full unit group of the adele ring $\mathbb A_K$ to $\mathbb C^\times$ whose associated function on ideles is continuous and trivial on the image of $K^\times$, and whose modulus is $\|z\|^{w}$ for a fixed real $w$, where $\|z\|$ denotes the value at $z$ of the Haar-scaling character of $\mathbb A_K$; let also $M_0, n_\rho \in \mathbb N$ and $\rho_1,\dots,\rho_{n_\rho}$ be families assigning to each finite place $v$ a character of $(K_v)^\times$. The assertion is that there exists $B_0 \in \mathbb N$ with the following property. Let $\iota E$ be a countable type and $\mu,\nu : \iota E \to \mathrm{Hom}(\mathbb A_K^\times,\mathbb C^\times)$ be such that each $\mu_e,\nu_e$ has absolute value $1$ everywhere, is trivial on the principal ideles, is continuous, satisfies $\mu_e(z)\nu_e(z)\|z\|^{w} = \xi K(z)$ for all $z$, and such that for $e \neq e'$ some idele of Haar-scaling character $1$ separates $\mu_e$ from $\mu_{e'}$ or $\nu_e$ from $\nu_{e'}$. Let $nE : \iota E \to \mathbb N$, let $\tau^\mu,\tau^\nu : \iota E \to \mathrm{InfinitePlace}(K) \to \mathbb R$ be such that at each infinite place $v$ and each $x \in (K_v)^\times$ with positive real and vanishing imaginary part under the embedding of $K_v$ into $\mathbb C$, the value of $\mu_e$ (resp. $\nu_e$) on the idele with component $x$ at $v$ and $1$ elsewhere equals $\|\cdot\|$ of that idele raised to $i\tau^\mu_{e,v}$ (resp. $i\tau^\nu_{e,v}$), and let $m^\mu,m^\nu : \iota E \to \mathrm{InfinitePlace}(K) \to \mathbb Z$ be such that on elements of absolute value $1$ those same values are the $m^\mu_{e,v}$-th (resp. $m^\nu_{e,v}$-th) power of the image of $x$ in $\mathbb C$. Assume that for every $e$ with $nE_e > 0$ one has $|m^\mu_{e,v}|, |m^\nu_{e,v}| \le M_0$ at all infinite places, that $\mu_e$ and $\nu_e$ are trivial on the units of the valuation ring at every finite place outside $SK$, and that for some indices $r,r'$ the restrictions of $\mu_e$ and $\nu_e$ to the integral units at each $v \in SK$ agree with $\rho_r$ and $\rho_{r'}$ respectively. Then for every natural $B \ge B_0$: each function $t \mapsto \bigl(1+\sum_{v\mid\infty}(|t+\tau^\mu_{e,v}|+|t-\tau^\nu_{e,v}|)\bigr)^{-B}$ is integrable on $\mathbb R$, and the families indexed by $e$ of the integrals of these functions, and of $\bigl(1+\sum_{v\mid\infty}(|\tau^\mu_{e,v}|+|\tau^\nu_{e,v}|)\bigr)^{-B}$, are summable, each term being replaced by $0$ unless $nE_e > 0$.
--
--   This is the convergence input for the continuous part of an adelic spectral decomposition: at fixed central character, level and collection of local types, the archimedean parameters of the admissible pairs of unitary idele class characters are spread out enough that polynomial-decay profiles of sufficiently high order are integrable and their sums converge. It feeds the bounds on cardinalities, archimedean parameters and weights used for orthonormal families of flat induced sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne
    (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
    (M₀ : ℕ) (nρ : ℕ) (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) :
    ∃ B₀ : ℕ, ∀ (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (τμ τν : ιE → InfinitePlace K → ℝ)
      (_hτ : ∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν e v : ℝ) : ℂ) * Complex.I))
      (mμ mν : ιE → InfinitePlace K → ℤ)
      (_hm : ∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v))
      (_hM₀ : ∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ))
      (_hram : ∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK →
          NumberField.TateGlobal.IsUnramifiedCharAt (μ e) v ∧ NumberField.TateGlobal.IsUnramifiedCharAt (ν e) v) ∧
        ∃ r r' : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e) v u = ρs r v u ∧ NumberField.TateGlobal.localChar (ν e) v u = ρs r' v u),
      ∀ B : ℕ, B₀ ≤ B →
        (∀ e : ιE, MeasureTheory.Integrable
          (fun t : ℝ => (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)))) ∧
        Summable (fun e : ιE => if 0 < nE e then
          ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)) else 0) ∧
        Summable (fun e : ιE => if 0 < nE e then
          (1 + ∑ v : InfinitePlace K, (|τμ e v| + |τν e v|)) ^ (-(B : ℝ)) else 0) := by sorry
