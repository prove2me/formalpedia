-- Prove2me | Theorems.Thm_AutomorphicForm_exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat
-- name    : AutomorphicForm.exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/183a7b70-6ec9-5862-8a31-163471d76e53
-- title:
--   Completed normalised intertwining operator across the axis
-- statement:
--   Fix a number field $K$, with the ideles $\mathbb{A}_K^\times$ and the adele ring carrying their Borel structures.
--
--   **Global data.** A finite set $S_K$ of finite places of $K$; a character $\xi_K$ of the full subgroup $\top$ of $\mathbb{A}_K^\times$ with values in $\mathbb{C}^\times$, continuous as a function of the idele (`hξc`) and trivial on the image of $K^\times$ under the map induced by $K \to \mathbb{A}_K$ (`hξt`); an ideal $N$ of $\mathcal{O}_K$ such that every prime $v$ with $v \mid N$ belongs to $S_K$ (`hN`); an archimedean type family `tysK`, that is, for each infinite place $w$ a number `card w` of representations `rep w i` of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$ on a space $\mathbb{C}^{n}$; and a real number $w$ with $\|\xi_K(z)\| = \|z\|^{w}$ for every idele $z$ (`hξw`), where $\|z\|$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value at $z$ of the distributive Haar character of $\mathbb{A}_K$.
--
--   Let $\alpha_m$ denote the homomorphism $\mathbb{A}_K^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring through $\mathbb{R}_{\geq 0} \to \mathbb{R}$, and assume all its values positive (`hαm`).
--
--   **Inducing characters.** Characters $\mu, \nu : \mathbb{A}_K^\times \to \mathbb{C}^\times$ that are unitary ($|\mu(x)| = |\nu(x)| = 1$ for all $x$: `_hμ`, `_hν`), trivial on principal ideles (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), and satisfy $\mu(z)\nu(z)\|z\|^{w} = \xi_K(z)$ for all $z$ (`_hμν`).
--
--   **Archimedean parameters.** Functions $\tau_\mu, \tau_\nu$ on the infinite places such that, at each infinite place $v$ and each unit $x$ of the completion $K_v$ whose image under `InfinitePlace.Completion.extensionEmbedding` has positive real part and vanishing imaginary part, the local component [`NumberField.TateGlobal.archLocalChar`](def/NumberField_TateGlobalZeta.html#L55) of $\mu$ (respectively $\nu$) at $v$ equals $\|\,\cdot\,\|^{\,i\tau_\mu(v)}$ (respectively $\|\,\cdot\,\|^{\,i\tau_\nu(v)}$) of the idele norm of the central idele attached to $x$ by [`NumberField.TateGlobal.archUnitHom`](def/NumberField_TateGlobalZeta.html#L35) (`_hτμ`, `_hτν`); and integers $m_\mu(v), m_\nu(v)$ such that on the units with $\|\,\cdot\,\| = 1$ the same local components are given by the $m_\mu(v)$-th, respectively $m_\nu(v)$-th, power of the embedding (`_hmμ`, `_hmν`).
--
--   **The flat section family.** A family $\psi_f : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ subject to the following hypotheses. For each $s$, $\psi_f(s)$ is an induced section for the pair of characters $\mu \cdot \alpha_m^{\,s + 1/2}$ and $\nu \cdot \alpha_m^{\,-(s+1/2)}$, i.e. $\psi_f(s)(bg) = \eta_1(b_{11})\eta_2(b_{22})\psi_f(s)(g)$ for $b$ in the adelic Borel subgroup (`_hψf`); $\psi_f(s)$ is `IsArchKFinite`, i.e. at every infinite place $w$ its right translates under `archRowIsometrySubgroup K w` (the image in $\mathrm{GL}_2(\mathbb{A}_K)$ of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$) satisfy `RightTranslatesSpanFinite` (`_hψfK`); $\psi_f(s)$ is `IsKfSmooth`, i.e. its stabiliser for right translation by the kernel of the archimedean projection `glArch` is open (`_hψff`); $(s,g) \mapsto \psi_f(s)(g)$ is continuous (`_hψfjc`); $s \mapsto \psi_f(s)(g)$ is entire for each $g$ (`_hψfhol`); at each infinite place $v$ there is a finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K v` containing $k \mapsto \psi_f(s)(gk)$ for all $s$ and $g$ (`_hψfKu`); flatness: $\psi_f(s)(k) = \psi_f(0)(k)$ for every $k$ in the maximal compact subgroup `adelicMaximalCompact K` (whose elements have finite part in `finiteIntegralGL2` and row-isometric components at all infinite places) (`_hψfflat`); right invariance under $\mathrm{principalLevel}(N) \sqcap \ker(\mathrm{glArch})$, where $\mathrm{principalLevel}(N)$ is the intersection of the level-one subgroup at $N$ with its conjugate by the Weyl element (`_hψflev`); $\psi_f(s)$ lies in the archimedean type-cut submodule `archCutSubmodule K tysK`, the intersection over infinite places $w$ of the sum of the isotypic submodules of the representations `tysK.rep w i` (`_hψfty`); and the normalisation $\int_{\mathbf{K}} \|\psi_f(0)(k)\|^2 \, d k \leq 1$ against the Haar measure `maximalCompactHaar K` (`_hψfn`).
--
--   **Eisenstein data.** A set $O_\psi \subseteq \mathbb{C}$ and functions $E_\psi, N_\psi : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that (`_hEψ`, a nine-fold conjunction): $O_\psi$ is open and preconnected and contains both the axis $\{\operatorname{Re} s = 0\}$ and the half-plane $\{\operatorname{Re} s > 1/2\}$; for each $g$ the functions $s \mapsto E_\psi(s)(g)$ and $s \mapsto N_\psi(s)(g)$ are analytic on a neighbourhood of $O_\psi$; both are jointly continuous on $O_\psi \times \mathrm{GL}_2(\mathbb{A}_K)$; for $\operatorname{Re} s > 1/2$, $E_\psi(s)(g) = \psi_f(s)(g) + \sum_{\xi \in K} \psi_f(s)(w\, u(\xi)\, g)$ with $w$ the image of $\begin{pmatrix} 0&1\\1&0\end{pmatrix}$ and $u(\xi)$ the upper unipotent at the principal adele $\xi$; and for $\operatorname{Re} s > 1/2$, $N_\psi(s)(g) = \int_{\mathbb{A}_K} \psi_f(s)(w^{-1} u(x) g)\, dx$ against `adelicAddHaar`.
--
--   **The completed $L$-factors.** Put $\chi = \mu\nu^{-1}$, and
--   $$P(w') = \prod_{v} \bigl(1 - \varepsilon_v\, \chi(\varpi_v)\, (\mathrm{N}v)^{-w'}\bigr)^{-1},$$
--   the product over all finite places, where $\varepsilon_v \chi(\varpi_v)$ is $\chi$ evaluated at the idele `uniformizerIdele K v` when $\chi$ is unramified at $v$ in the sense of [`NumberField.TateGlobal.IsUnramifiedCharAt`](def/NumberField_TateGlobalZeta.html#L59) (its local component is trivial on the units of the valuation ring) and is $0$ otherwise, and $\mathrm{N}v$ is the absolute norm of $v$; further
--   $$\gamma(w') = \prod_{v \mid \infty} \begin{cases} \Gamma_{\mathbb{R}}\bigl(w' + i(\tau_\mu(v) - \tau_\nu(v)) + \left(|m_\mu(v) - m_\nu(v)| \bmod 2\right)\bigr), & v \text{ real},\\ \Gamma_{\mathbb{C}}\bigl(w' + i(\tau_\mu(v) - \tau_\nu(v)) + |m_\mu(v) - m_\nu(v)|/2\bigr), & v \text{ complex},\end{cases}$$
--   and let $c$ be the inverse of the volume of the box `adelicBox K` for `adelicAddHaar`, viewed in $\mathbb{C}$.
--
--   **Conclusion.** There exist $\delta \in \mathbb{R}$ and $R : \mathbb{C} \to \mathbf{K} \to \mathbb{C}$, with $\mathbf{K} =$ `adelicMaximalCompact K`, such that:
--
--   1. $\delta > 0$;
--
--   2. for every $k \in \mathbf{K}$ the function $s \mapsto R(s)(k)$ is analytic on a neighbourhood of $\{\operatorname{Re} s > -\delta\}$;
--
--   3. $(s,k) \mapsto R(s)(k)$ is continuous on $\{\operatorname{Re} s > -\delta\} \times \mathbf{K}$;
--
--   4. if $\chi$ differs from [`NumberField.TateGlobal.normPowChar K`](def/NumberField_NormPowChar.html#L22) $\tau_0$, i.e. from $\|\,\cdot\,\|^{\,i\tau_0}$, for every real $\tau_0$, then for every entire $\Lambda : \mathbb{C} \to \mathbb{C}$ with $\Lambda(w') = \gamma(w')P(w')$ on $\operatorname{Re} w' > 1$ both of the following hold: for all $s \in O_\psi$ with $\operatorname{Re} s > -\delta$ and all $k \in \mathbf{K}$,
--   $$\Lambda(2s+1)\,\bigl(c\,N_\psi(s)(k)\bigr) = \Lambda(2s)\,R(s)(k),$$
--   and for all $s$ with $\operatorname{Re} s > 1/2$ and all $k \in \mathbf{K}$,
--   $$\Lambda(2s)\,R(s)(k) = \Lambda(2s+1)\,\Bigl(c \int_{\mathbb{A}_K} \psi_f(s)(w^{-1}u(x)k)\,dx\Bigr);$$
--
--   5. for every real $\tau_0$ with $\chi = \|\,\cdot\,\|^{\,i\tau_0}$ and every entire $\Lambda_Q$ with $\Lambda_Q(w') = (w' + i\tau_0)\bigl(w' - (1 - i\tau_0)\bigr)\gamma(w')P(w')$ on $\operatorname{Re} w' > 1$, both of the following hold: for all $s \in O_\psi$ with $\operatorname{Re} s > -\delta$ and all $k \in \mathbf{K}$,
--   $$(2s + i\tau_0 - 1)\,\Lambda_Q(2s+1)\,\bigl(c\,N_\psi(s)(k)\bigr) = (2s + i\tau_0 + 1)\,\Lambda_Q(2s)\,R(s)(k),$$
--   and for all $s$ with $\operatorname{Re} s > 1/2$ and all $k \in \mathbf{K}$,
--   $$(2s + i\tau_0 + 1)\,\Lambda_Q(2s)\,R(s)(k) = (2s + i\tau_0 - 1)\,\Lambda_Q(2s+1)\,\Bigl(c \int_{\mathbb{A}_K} \psi_f(s)(w^{-1}u(x)k)\,dx\Bigr).$$
--
--   The function $R$ is thus the completed normalisation of the Weyl intertwining integral restricted to the maximal compact subgroup: on $\operatorname{Re} s > 1/2$ it is pinned by the second identity of each case, and the first identity transports that relation to the continuation $N_\psi$ on the part of $O_\psi$ with $\operatorname{Re} s > -\delta$, in particular across the axis $\operatorname{Re} s = 0$. No assertion is made about $R$ outside $\mathbf{K}$, nor about $E_\psi$.
--
--   The statement provides the analytic continuation, across the unitary axis, of the normalised (Gindikin–Karpelevich) intertwining operator $M(s)$ attached to a flat level-$N$ section of the induced representation on $\mathrm{GL}_2(\mathbb{A}_K)$: the completed Hecke $L$-function $\Lambda$ of $\chi = \mu\nu^{-1}$ (with the extra linear factors in the norm-power case, where the $L$-function has poles) clears the poles of the local factors, leaving an operator holomorphic on a half-plane $\operatorname{Re} s > -\delta$. It is used by the two results that combine this factorisation identity with the $L^2$ bound on the maximal compact subgroup for the constant term of the Eisenstein series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_analyticOnNhd_normalizedIntertwining_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_of_flat
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g)),
    let χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ * ν⁻¹
    let P : ℂ → ℂ := fun w' => ∏' v : HeightOneSpectrum (𝓞 K),
        (1 - (if NumberField.TateGlobal.IsUnramifiedCharAt χ v then ((χ (uniformizerIdele K v) : ℂˣ) : ℂ) else 0) *
          (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-w')))⁻¹
    let γ : ℂ → ℂ := fun w' => ∏ v : InfinitePlace K,
        (if v.IsReal then Complex.Gammaℝ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs % 2 : ℕ) : ℂ))
          else Complex.Gammaℂ (w' + ((τμ v - τν v : ℝ) : ℂ) * Complex.I + (((mμ v - mν v).natAbs : ℕ) : ℂ) / 2))
    let c : ℂ := ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹
    ∃ (δ : ℝ) (R : ℂ → adelicMaximalCompact K → ℂ), 0 < δ ∧
      (∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -δ < s.re}) ∧
      ContinuousOn (fun p : ℂ × adelicMaximalCompact K => R p.1 p.2) ({s : ℂ | -δ < s.re} ×ˢ Set.univ) ∧
      ((∀ τ₀ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar K τ₀) →
        ∀ (Λ : ℂ → ℂ), Differentiable ℂ Λ → (∀ w' : ℂ, 1 < w'.re → Λ w' = γ w' * P w') →
          (∀ s : ℂ, s ∈ Oψ → -δ < s.re → ∀ k : adelicMaximalCompact K,
            Λ (2 * s + 1) * (c * Nψ s (k : AdelicGL2 (𝓞 K) K)) = Λ (2 * s) * R s k) ∧
          (∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            Λ (2 * s) * R s k = Λ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K)))) ∧
      (∀ τ₀ : ℝ, χ = NumberField.TateGlobal.normPowChar K τ₀ →
        ∀ (ΛQ : ℂ → ℂ), Differentiable ℂ ΛQ →
          (∀ w' : ℂ, 1 < w'.re → ΛQ w' = (w' + ((τ₀ : ℝ) : ℂ) * Complex.I) * (w' - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ w' * P w')) →
          (∀ s : ℂ, s ∈ Oψ → -δ < s.re → ∀ k : adelicMaximalCompact K,
            (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * ΛQ (2 * s + 1) * (c * Nψ s (k : AdelicGL2 (𝓞 K) K))
              = (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * ΛQ (2 * s) * R s k) ∧
          (∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * ΛQ (2 * s) * R s k
              = (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * ΛQ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K)))) := by sorry
