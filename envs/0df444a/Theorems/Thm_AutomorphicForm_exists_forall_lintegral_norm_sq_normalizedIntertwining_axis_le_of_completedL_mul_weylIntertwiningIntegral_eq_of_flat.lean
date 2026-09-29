-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
-- name    : AutomorphicForm.exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/066df6a5-a032-56b5-9e84-29c256e9f68b
-- title:
--   Uniform axis L²(K) bound for the normalised intertwining operator
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$, the adele ring $\mathbb A_K =$ `AdeleRing (𝓞 K) K` carries its Borel $\sigma$-algebra (`adeleBorel`) and the additive Haar measure `adelicAddHaar`, the idele group $\mathbb A_K^\times$ carries a Borel measurable structure, and $\mathrm{GL}_2(\mathbb A_K) =$ `AdelicGL2 (𝓞 K) K` carries the Borel structure `glBorel`. The homomorphism $\alpha_m : \mathbb A_K^\times \to \mathbb R^\times$ is the one induced by the module character `distribHaarChar` of $\mathbb A_K$ through the passage from non-negative reals to reals, i.e. the idele norm read as a homomorphism to $\mathbb R^\times$.
--
--   **Fixed data.** A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top \le \mathbb A_K^\times$ to $\mathbb C^\times$ such that $z \mapsto \xi_K(z)$ is continuous (`hξc`) and $\xi_K$ is trivial on the image of $K^\times$ under the map induced by $K \to \mathbb A_K$ (`hξt`); an ideal $N \subseteq \mathcal O_K$ all of whose prime divisors lie in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place $v$ a natural number and that many representations of the row-isometry subgroup of $\mathrm{GL}_2(K_v)$ on finite-dimensional complex spaces (`ArchTypeFamily`); and a real number $w$ with $\|\xi_K(z)\| = \mathrm{ideleNorm}_K(z)^{w}$ for all $z$ (`hξw`), where $\mathrm{ideleNorm}_K$ is the real value of `distribHaarChar`.
--
--   **Assertion.** There exist a real number $C$ and a natural number $A$ with $C > 0$ such that the following holds for every further choice of data, the constants $C$ and $A$ thus being uniform in all of it.
--
--   *Character data.* A proof `hαm` that $\alpha_m(x) > 0$ for all $x$; homomorphisms $\mu, \nu : \mathbb A_K^\times \to \mathbb C^\times$ which are unitary ($\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$), trivial on the image of $K^\times$, continuous, and satisfy $\mu(z)\nu(z)\,\mathrm{ideleNorm}_K(z)^{w} = \xi_K(z)$ for all $z$.
--
--   *Archimedean parameters.* Functions $\tau_\mu, \tau_\nu$ from the infinite places to $\mathbb R$ such that, at each infinite place $v$ and each $x \in K_v^\times$ whose image under the extension embedding of $K_v$ has positive real part and vanishing imaginary part, the local character of $\mu$ (respectively $\nu$) at $v$ — that is, $\mu$ (respectively $\nu$) composed with the inclusion of $K_v^\times$ as ideles concentrated at $v$ — equals $\mathrm{ideleNorm}_K$ of that idele raised to the power $\tau_\mu(v)\,i$ (respectively $\tau_\nu(v)\,i$); and functions $m_\mu, m_\nu$ from the infinite places to $\mathbb Z$ such that, for $x \in K_v^\times$ of absolute value $1$, the same local characters are given by the $m_\mu(v)$-th (respectively $m_\nu(v)$-th) power of the image of $x$.
--
--   *The section family.* A family $\psi_f : \mathbb C \to \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$ subject to the following hypotheses. For each $s$, $\psi_f(s)$ is an induced section for the pair $(\eta_1(s), \eta_2(s)) = (\mu \cdot \alpha_m^{\,s + 1/2},\ \nu \cdot \alpha_m^{-(s+1/2)})$, i.e. $\psi_f(s)(bg) = \eta_1(s)(b_{11})\,\eta_2(s)(b_{22})\,\psi_f(s)(g)$ for every $b$ with vanishing lower-left entry and every $g$; each $\psi_f(s)$ is `IsArchKFinite`, the condition `RightTranslatesSpanFinite` for the image of the row-isometry subgroup of $\mathrm{GL}_2(K_v)$ in $\mathrm{GL}_2(\mathbb A_K)$ at every infinite place $v$; each $\psi_f(s)$ is `IsKfSmooth`, i.e. a smooth vector for the group of elements with trivial archimedean part (the kernel of `glArch`), so that its stabiliser under right translation by that group is open; the map $(s,g) \mapsto \psi_f(s)(g)$ is jointly continuous; $s \mapsto \psi_f(s)(g)$ is entire for each $g$; for each infinite place $v$ there is a finite-dimensional subspace $W$ of functions on the row-isometry subgroup at $v$ containing all functions $k \mapsto \psi_f(s)(gk)$ ($s \in \mathbb C$, $g \in \mathrm{GL}_2(\mathbb A_K)$); the flatness condition $\psi_f(s)(k) = \psi_f(0)(k)$ for every $s$ and every $k$ in the adelic maximal compact subgroup $\mathbf K$, consisting of those elements whose finite part lies in `finiteIntegralGL2` and whose component at each infinite place is a row isometry; right invariance under the group $\mathrm{principalLevel}(N) \sqcap \mathrm{finiteAdelicGL2Subgroup}$, where $\mathrm{principalLevel}(N)$ is the intersection of the level-$N$ subgroup with its conjugate by the antidiagonal Weyl element; membership $\psi_f(s) \in \mathrm{archCutSubmodule}(\mathrm{tys}_K)$ for every $s$, the intersection over infinite places of the sums of the type submodules attached to the given representations; and the normalisation $\int_{\mathbf K} \|\psi_f(0)(k)\|^2 \, dk \le 1$ with respect to the Haar measure `maximalCompactHaar` on $\mathbf K$.
--
--   *The continuation datum.* A set $O_\psi \subseteq \mathbb C$ and families $E_\psi, N_\psi$ subject to the nine-fold hypothesis `_hEψ`: $O_\psi$ is open and preconnected, contains the imaginary axis $\{\operatorname{Re} s = 0\}$ and the half-plane $\{\operatorname{Re} s > 1/2\}$; for each $g$ the functions $s \mapsto E_\psi(s)(g)$ and $s \mapsto N_\psi(s)(g)$ are analytic on a neighbourhood of $O_\psi$; both $(s,g) \mapsto E_\psi(s)(g)$ and $(s,g) \mapsto N_\psi(s)(g)$ are continuous on $O_\psi \times \mathrm{univ}$; for $\operatorname{Re} s > 1/2$ and all $g$, $E_\psi(s)(g) = \psi_f(s)(g) + \sum_{\xi \in K}' \psi_f(s)\bigl(w\,u(\xi)\,g\bigr)$, where $w$ is the adelic antidiagonal Weyl element and $u(\xi)$ the upper unipotent matrix with entry the image of $\xi$; and for $\operatorname{Re} s > 1/2$ and all $g$, $N_\psi(s)(g)$ equals the Weyl intertwining integral $\int_{\mathbb A_K} \psi_f(s)(w^{-1} u(x) g)\,dx$ with respect to `adelicAddHaar`.
--
--   With this data set $\chi = \mu\nu^{-1}$; let
--   $$P(w') = \prod_{v}' \bigl(1 - \chi_v\,(\mathrm{Nm}\, v)^{-w'}\bigr)^{-1},$$
--   the product over the finite places, where $\chi_v$ is $\chi$ evaluated at the uniformizer idele at $v$ if $\chi$ is unramified at $v$ (its local character trivial on the units of the valuation ring) and $0$ otherwise, and $\mathrm{Nm}\,v$ is the absolute norm of the prime ideal; let
--   $$\gamma(w') = \prod_{v \mid \infty} \begin{cases} \Gamma_{\mathbb R}\bigl(w' + (\tau_\mu(v) - \tau_\nu(v))i + (|m_\mu(v) - m_\nu(v)| \bmod 2)\bigr), & v \text{ real},\\ \Gamma_{\mathbb C}\bigl(w' + (\tau_\mu(v) - \tau_\nu(v))i + |m_\mu(v) - m_\nu(v)|/2\bigr), & v \text{ complex};\end{cases}$$
--   let $c$ be the inverse of the real volume, viewed in $\mathbb C$, of the adelic box (the product of the fundamental domain for the lattice at the infinite places with the integral finite adeles) for `adelicAddHaar`; and let
--   $$D(y) = \sum_{v \mid \infty} \bigl(|y + \tau_\mu(v)| + |y - \tau_\nu(v)| + |m_\mu(v)| + |m_\nu(v)|\bigr).$$
--
--   *The operator $R$ and its pinning.* For every real $\delta > 0$ and every $R : \mathbb C \to \mathbf K \to \mathbb C$ with $\delta > 0$, such that for each $k \in \mathbf K$ the function $s \mapsto R(s)(k)$ is analytic on a neighbourhood of $\{\operatorname{Re} s > -\delta\}$ and $(s,k) \mapsto R(s)(k)$ is continuous on $\{\operatorname{Re} s > -\delta\} \times \mathrm{univ}$, and such that the following two pinning conditions hold:
--
--   (i) if $\chi$ is not equal to the character $x \mapsto \mathrm{ideleNorm}_K(x)^{i\tau_0}$ for any real $\tau_0$, then for every entire $\Lambda$ with $\Lambda(w') = \gamma(w')P(w')$ on $\operatorname{Re} w' > 1$, every $s$ with $\operatorname{Re} s > 1/2$ and every $k \in \mathbf K$,
--   $$\Lambda(2s)\,R(s)(k) = \Lambda(2s+1)\bigl(c \cdot M(s)(k)\bigr),$$
--   where $M(s)(k)$ denotes the Weyl intertwining integral of $\psi_f(s)$ at $k$;
--
--   (ii) for every real $\tau_0$ with $\chi$ equal to $x \mapsto \mathrm{ideleNorm}_K(x)^{i\tau_0}$, for every entire $\Lambda_Q$ with $\Lambda_Q(w') = (w' + \tau_0 i)\bigl(w' - (1 - \tau_0 i)\bigr)\gamma(w')P(w')$ on $\operatorname{Re} w' > 1$, every $s$ with $\operatorname{Re} s > 1/2$ and every $k \in \mathbf K$,
--   $$(2s + \tau_0 i + 1)\,\Lambda_Q(2s)\,R(s)(k) = (2s + \tau_0 i - 1)\,\Lambda_Q(2s+1)\bigl(c \cdot M(s)(k)\bigr);$$
--
--   the conclusion is that for every real $t$,
--   $$\int_{\mathbf K} \|R(it)(k)\|^2 \, dk \le \bigl(C\,(1 + D(t))^{A}\bigr)^2,$$
--   the integral being the Bochner integral with respect to `maximalCompactHaar`.
--
--   This is the $L^2(\mathbf K)$ bound on the unitary axis for the completed and normalised Weyl intertwining operator attached to an Eisenstein datum of fixed level $N$ and fixed archimedean types, with a polynomial dependence on the archimedean parameters and with constants independent of the inducing characters $\mu,\nu$ and of the section family $\psi_f$. It feeds the combined continuation-and-bound statement [`AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat`](thm.html#AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat), where the functional equation of the completed $L$-function of $\chi = \mu\nu^{-1}$ and the resulting spectral decomposition of Eisenstein series for $\mathrm{GL}_2$ over $K$ are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat.lean

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

theorem AutomorphicForm.exists_forall_lintegral_norm_sq_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
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
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧
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
    let D : ℝ → ℝ := fun y => ∑ v : InfinitePlace K, (|y + τμ v| + |y - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))
    ∀ (δ : ℝ) (R : ℂ → adelicMaximalCompact K → ℂ), 0 < δ →
      (∀ k : adelicMaximalCompact K, AnalyticOnNhd ℂ (fun s => R s k) {s : ℂ | -δ < s.re}) →
      ContinuousOn (fun p : ℂ × adelicMaximalCompact K => R p.1 p.2) ({s : ℂ | -δ < s.re} ×ˢ Set.univ) →
      ((∀ τ₀ : ℝ, χ ≠ NumberField.TateGlobal.normPowChar K τ₀) →
        ∀ (Λ : ℂ → ℂ), Differentiable ℂ Λ → (∀ w' : ℂ, 1 < w'.re → Λ w' = γ w' * P w') →
          ∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            Λ (2 * s) * R s k = Λ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K))) →
      (∀ τ₀ : ℝ, χ = NumberField.TateGlobal.normPowChar K τ₀ →
        ∀ (ΛQ : ℂ → ℂ), Differentiable ℂ ΛQ →
          (∀ w' : ℂ, 1 < w'.re → ΛQ w' = (w' + ((τ₀ : ℝ) : ℂ) * Complex.I) * (w' - ((1 : ℂ) - ((τ₀ : ℝ) : ℂ) * Complex.I)) * (γ w' * P w')) →
          ∀ s : ℂ, 1 / 2 < s.re → ∀ k : adelicMaximalCompact K,
            (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I + 1) * ΛQ (2 * s) * R s k
              = (2 * s + ((τ₀ : ℝ) : ℂ) * Complex.I - 1) * ΛQ (2 * s + 1) * (c * weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) (k : AdelicGL2 (𝓞 K) K))) →
      ∀ t : ℝ, (∫ k, ‖R ((t : ℂ) * Complex.I) k‖ ^ 2 ∂(maximalCompactHaar K)) ≤ (C * (1 + D t) ^ A) ^ 2 := by sorry
