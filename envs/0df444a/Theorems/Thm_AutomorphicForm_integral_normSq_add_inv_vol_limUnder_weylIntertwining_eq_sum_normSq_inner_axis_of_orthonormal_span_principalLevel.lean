-- Prove2me | Theorems.Thm_AutomorphicForm_integral_normSq_add_inv_vol_limUnder_weylIntertwining_eq_sum_normSq_inner_axis_of_orthonormal_span_principalLevel
-- name    : AutomorphicForm.integral_normSq_add_inv_vol_limUnder_weylIntertwining_eq_sum_normSq_inner_axis_of_orthonormal_span_principalLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/5ff61f06-a05f-5532-b546-af65a412250a
-- title:
--   Pointwise Parseval on the unitary axis for induced sections
-- statement:
--   Let $K$ be a number field, let $N$ be a nonzero ideal of $\mathcal{O}_K$, and let `tysK` be an archimedean type family for $K$, i.e. a number $\mathrm{card}(w)$ of representations $\rho$ of the row-isometry group of $K_w$ on a space $\mathbb{C}^{m}$ for each infinite place $w$; the associated cut space `archCutSubmodule K tysK` is the intersection over $w$ of the sum over $i < \mathrm{card}(w)$ of the corresponding type subspaces of functions on $\mathrm{GL}_2(\mathbb{A}_K)$. Write $\alpha_m$ for the homomorphism from the idele group $(\mathbb{A}_K)^\times$ to $\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ through $\mathbb{R}_{\ge 0} \to \mathbb{R}$; the adele ring is equipped with its Borel $\sigma$-algebra and $\mathrm{GL}_2(\mathbb{A}_K)$ with the Borel structure `glBorel`. The hypothesis `hαm` asserts that $\alpha_m(x) > 0$ for every idele $x$.
--
--   The data and hypotheses are as follows.
--
--   (1) Base characters. Two homomorphisms $\mu, \nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$, each unitary (all values of absolute value $1$), each trivial on the principal ideles coming from $K^\times$, and each continuous as a $\mathbb{C}$-valued function.
--
--   (2) A family of sections. A natural number $n$ and functions $\varphi_j(s) : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ for $j \in \mathrm{Fin}\,n$, $s \in \mathbb{C}$, subject to: `_hφE`, each $\varphi_j(s)$ is an induced section for the pair $(\eta_1, \eta_2) = (\mu \cdot \alpha_m^{\,s+1/2},\ \nu \cdot \alpha_m^{\,-(s+1/2)})$, that is $\varphi_j(s)(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\varphi_j(s)(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry zero) and every $g$; `_hφEK`, each $\varphi_j(s)$ is archimedean $K$-finite, i.e. at every infinite place $w$ its right translates under the archimedean row-isometry subgroup span a finite-dimensional space; `_hφEf`, each $\varphi_j(s)$ is $K_f$-smooth, i.e. its stabiliser under right translation inside the subgroup of elements with trivial archimedean part is open; `_hφEjc`, joint continuity of $(s,g) \mapsto \varphi_j(s)(g)$; `_hφEhol`, holomorphy of $s \mapsto \varphi_j(s)(g)$ on all of $\mathbb{C}$ for each $g$; `_hφEKu`, a uniform form of $K$-finiteness, namely for each $j$ and each infinite place $w$ a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $w$ such that $k \mapsto \varphi_j(s)(gk)$ lies in $W$ for all $s$ and $g$; `_hφEflat`, flatness on the maximal compact subgroup, $\varphi_j(s)(k) = \varphi_j(0)(k)$ for every $k$ in `adelicMaximalCompact K` (finite part integral, all archimedean components row isometries); `_hφElev`, right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; `_hφEty`, $\varphi_j(s) \in$ `archCutSubmodule K tysK` for all $s$; `_hφEon`, orthonormality at $s = 0$ with respect to the Haar measure `maximalCompactHaar K` on the maximal compact subgroup, $\int_{\mathbf{K}} \varphi_i(0)(k)\,\overline{\varphi_j(0)(k)}\,dk = \delta_{ij}$; and `_hφEspan`, spanning on the unitary axis: for every $t \in \mathbb{R}$, any $\varphi_0$ that is an induced section for the pair attached to $s = it$, continuous, archimedean $K$-finite, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and lying in `archCutSubmodule K tysK`, belongs to the $\mathbb{C}$-span of $\{\varphi_j(it) : j \in \mathrm{Fin}\,n\}$.
--
--   (3) Continuation data for the family. Sets $O_j \subseteq \mathbb{C}$ and functions $E_j, N_j : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that, for each $j$ (hypothesis `_hEE`, a conjunction of nine clauses): $O_j$ is open and preconnected and contains both the line $\{\mathrm{Re}\,s = 0\}$ and the half-plane $\{\mathrm{Re}\,s > 1/2\}$; for each $g$, $s \mapsto E_j(s)(g)$ and $s \mapsto N_j(s)(g)$ are analytic on a neighbourhood of $O_j$; $(s,g) \mapsto E_j(s)(g)$ and $(s,g) \mapsto N_j(s)(g)$ are continuous on $O_j \times \mathrm{GL}_2(\mathbb{A}_K)$; for $\mathrm{Re}\,s > 1/2$ and all $g$, $E_j(s)(g) = \varphi_j(s)(g) + \sum_{\xi \in K}' \varphi_j(s)(w\,u(\xi)\,g)$, where $w$ is the adelic Weyl element $\begin{pmatrix} 0 & 1 \\ 1 & 0\end{pmatrix}$ and $u(\xi) = \begin{pmatrix} 1 & \xi \\ 0 & 1\end{pmatrix}$; and for $\mathrm{Re}\,s > 1/2$ and all $g$, $N_j(s)(g) = \int_{\mathbb{A}_K} \varphi_j(s)(w^{-1} u(x) g)\,dx$ with respect to the additive Haar measure `adelicAddHaar (𝓞 K) K`.
--
--   (4) Shifted characters and two further families. A real number $\tau$ and characters $\mu', \nu'$ with $\mu' = \mu \cdot \lVert\cdot\rVert^{i\tau}$ and $\nu' = \nu \cdot \lVert\cdot\rVert^{-i\tau}$, where $\lVert\cdot\rVert^{i\tau}$ is [`NumberField.TateGlobal.normPowChar K τ`](def/NumberField_NormPowChar.html#L22), sending an idele $x$ to $(\mathrm{ideleNorm}\,x)^{i\tau}$; $\mu'$ and $\nu'$ are assumed unitary, trivial on principal ideles and continuous. A family $\psi_1(s)$ of induced sections for the pair $(\mu' \cdot \alpha_m^{\,s+1/2},\ \nu' \cdot \alpha_m^{\,-(s+1/2)})$, jointly continuous, holomorphic in $s$ for each $g$, archimedean $K$-finite, $K_f$-smooth, satisfying the same uniform finite-dimensionality condition at each infinite place, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` and lying in `archCutSubmodule K tysK` for every $s$. Characters $\mu_2, \nu_2$ with $\mu_2 = \nu'$ and $\nu_2 = \mu'$, and a family $\psi_2(s)$ of induced sections for the reversed pair $(\nu' \cdot \alpha_m^{\,s+1/2},\ \mu' \cdot \alpha_m^{\,-(s+1/2)})$ satisfying exactly the same list of conditions as $\psi_1$.
--
--   (5) Meromorphic continuation for $\psi_2$. A function $M_2 : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ such that for every $g$ the function $s \mapsto M_2(s)(g)$ is meromorphic in normal form on all of $\mathbb{C}$, and $M_2(s)(g) = \int_{\mathbb{A}_K} \psi_2(s)(w^{-1} u(x) g)\,dx$ for $\mathrm{Re}\,s > 1/2$.
--
--   Then, for every $t \in \mathbb{R}$, the following identity holds. Write $v = \bigl(\mathrm{adelicAddHaar}(\mathrm{adelicBox}\,K)\bigr)^{\mathrm{toReal}}$, the volume of the adelic box (the product of the fundamental domain of the Minkowski lattice at the infinite places with the integral finite adeles), regarded as a complex number, let all integrals in $k$ be over `adelicMaximalCompact K` with respect to `maximalCompactHaar K`, and put
--   $$A(k) = \psi_1(it)(k) + v^{-1}\, \lim_{s \to -it,\ s \neq -it} M_2(s)(k),$$
--   the limit being `Filter.limUnder` along the punctured neighbourhood filter of $-it$. Then
--   $$\int_{\mathbf{K}} A(k)\,\overline{A(k)}\,dk = \sum_{j \in \mathrm{Fin}\,n} B_j\,\overline{B_j},$$
--   where, with $t' = t + \tau$,
--   $$B_j = \int_{\mathbf{K}} \psi_1(it)(k)\,\overline{\varphi_j(it')(k)}\,dk \ +\ \int_{\mathbf{K}} \psi_2(-it)(k)\,\overline{\,v^{-1} N_j(it')(k)\,}\,dk.$$
--   Here $it$, $-it$ and $it'$ denote the complex numbers $(t:\mathbb{R})\cdot i$, $-((t:\mathbb{R})\cdot i)$ and $((t+\tau : \mathbb{R}))\cdot i$ respectively.
--
--   This is the pointwise-in-$t$ Parseval step on the unitary axis: the $\mathbf{K}$-inner-product square norm of the continued section $\psi_1(it) + v^{-1}M_2(-it)$ is expressed through its coordinates against the orthonormal family $\varphi_j(it')$ together with the intertwining continuations $N_j(it')$ paired with $\psi_2(-it)$. It is used, after integration in $t$ and summation, in [`AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_setIntegral_normSq_pseudoEisenstein_sub_residualProj_eq_mul_sum_integral_sum_normSq_inner_axis_of_matched_paleyWiener), the Plancherel identity for pseudo-Eisenstein series in Paley–Wiener coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_normSq_add_inv_vol_limUnder_weylIntertwining_eq_sum_normSq_inner_axis_of_orthonormal_span_principalLevel.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
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
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_normSq_add_inv_vol_limUnder_weylIntertwining_eq_sum_normSq_inner_axis_of_orthonormal_span_principalLevel
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tysK : ArchTypeFamily K) :
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
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ i j, ∫ k, φE i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin n => φE j ((t : ℂ) * Complex.I)))
      (OE : Fin n → Set ℂ) (EE NE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (j : Fin n),
      IsOpen (OE j) ∧ IsPreconnected (OE j) ∧ {s : ℂ | s.re = 0} ⊆ (OE j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE j s g) (OE j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE j s g) (OE j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE j p.1 p.2) ((OE j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE j s g = φE j s g + ∑' ξ : K, φE j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE j s) g))
      (τ : ℝ) (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hem : μ' = μ * NumberField.TateGlobal.normPowChar K τ ∧ ν' = ν * (NumberField.TateGlobal.normPowChar K τ)⁻¹)
      (_hμ' : IsUnitaryChar (𝓞 K) K μ') (_hν' : IsUnitaryChar (𝓞 K) K ν')
      (_hμ'ic : IsIdeleClassChar (𝓞 K) K μ') (_hν'ic : IsIdeleClassChar (𝓞 K) K ν')
      (_hμ'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ))
      (_hν'c : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ))
      (ψ₁ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ' αm hαm s) (etaSnd ν' αm hαm s) (ψ₁ s))
      (_hψ₁jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ₁ p.1 p.2))
      (_hψ₁hol : ∀ g, Differentiable ℂ (fun s => ψ₁ s g))
      (_hψ₁K : ∀ s, IsArchKFinite K (ψ₁ s)) (_hψ₁sm : ∀ s, IsKfSmooth K (ψ₁ s))
      (_hψ₁Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ₁ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψ₁lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ₁ s (g * u) = ψ₁ s g)
      (_hψ₁ty : ∀ (s : ℂ), ψ₁ s ∈ archCutSubmodule K tysK)
      (μ₂ ν₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (_hrev : μ₂ = ν' ∧ ν₂ = μ')
      (ψ₂ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ₂ αm hαm s) (etaSnd ν₂ αm hαm s) (ψ₂ s))
      (_hψ₂jc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ₂ p.1 p.2))
      (_hψ₂hol : ∀ g, Differentiable ℂ (fun s => ψ₂ s g))
      (_hψ₂K : ∀ s, IsArchKFinite K (ψ₂ s)) (_hψ₂sm : ∀ s, IsKfSmooth K (ψ₂ s))
      (_hψ₂Ku : ∀ (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ₂ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψ₂lev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ₂ s (g * u) = ψ₂ s g)
      (_hψ₂ty : ∀ (s : ℂ), ψ₂ s ∈ archCutSubmodule K tysK)
      (Mc₂ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hMc₂ : ∀ g : AdelicGL2 (𝓞 K) K, MeromorphicNFOn (fun s : ℂ => Mc₂ s g) Set.univ ∧
        ∀ s : ℂ, (1 / 2 : ℝ) < s.re → Mc₂ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψ₂ s) g)
      (t : ℝ),
    (∫ k, (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)
              + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                  (fun s : ℂ => Mc₂ s (k : AdelicGL2 (𝓞 K) K)))
          * conj
            (ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)
              + ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                Filter.limUnder (𝓝[≠] (-((t : ℂ) * Complex.I)))
                  (fun s : ℂ => Mc₂ s (k : AdelicGL2 (𝓞 K) K)))
        ∂(maximalCompactHaar K)) =
      ∑ j : Fin n,
        ((∫ k, ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
                  conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                    NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
        conj ((∫ k, ψ₁ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
                  conj (φE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
              ∫ k, ψ₂ (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) *
                  conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ *
                    NE j ((((t + τ : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by sorry
