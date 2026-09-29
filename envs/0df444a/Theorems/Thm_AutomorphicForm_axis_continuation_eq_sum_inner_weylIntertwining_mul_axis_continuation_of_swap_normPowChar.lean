-- Prove2me | Theorems.Thm_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
-- name    : AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/cabb4a15-b877-567f-bc53-d2b67cb53b00
-- title:
--   Functional equation of the Eisenstein axis continuation, frame form
-- statement:
--   The setting is a number field $K$ with ring of integers $\mathcal O_K$, together with the following data.
--
--   **Truncation and Siegel data.** Reals $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K$ of adelic matrices in $\mathrm{GL}_2(\mathbb A_K)$ on which no condition is imposed; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}$, $d_{1K}<d_{2K}$; a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb A_K)$; and the hypothesis `hcovK`, which says that the union $\bigcup_{x\in T_K}\,(\,\cdot\,x)$-translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` covers $\mathrm{GL}_2(\mathbb A_K)$ modulo the centre: every $g$ can be written, after multiplication on the left by a global point $\gamma\in\mathrm{GL}_2(K)$ and on the right by a central scalar $z$ in the ideles, as an element of that union. The Siegel set itself consists of those $g$ whose finite part is integral, whose archimedean components at every infinite place $w$ have local height $\ge c_K$ and window $x$-coordinate with `xWindowSq` $\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$.
--
--   **Centre data.** A Haar measure $\nu_{ZK}$ on the idele units $\mathbb A_K^\times$ (with a measurable structure making it Borel) and a set $\Omega_K$ which is a fundamental domain for the action of the image of $K^\times$ in $\mathbb A_K^\times$ with respect to $\nu_{ZK}$.
--
--   **Character and level data.** A finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top\le\mathbb A_K^\times$ to $\mathbb C^\times$, which is continuous (`hξc`), trivial on the image of $K^\times$ (`hξt`) and of absolute value $1$ at every idele (`hξu`); an ideal $N\subseteq\mathcal O_K$ such that every finite place $v$ whose prime divides $N$ lies in $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place $w$ a natural number and that many representations of the row-isometry group of $K_w$.
--
--   The statement then introduces $\alpha_m:\mathbb A_K^\times\to\mathbb R^\times$, the unit-valued homomorphism obtained from the module (distributive Haar) character of $\mathbb A_K$ via $\mathbb R_{\ge0}\to\mathbb R$, fixes the Borel structure `adeleBorel` on $\mathbb A_K$, and assumes `hαm`: $\alpha_m(x)>0$ for all $x$.
--
--   The carrier data used throughout is the record $P=$ `productionPinsOf` $K$ with: domain the canonical truncation domain `canonicalTruncationDomain K α β` attached to $\alpha<\beta$, level subgroups $M\mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, Hecke generators $v\mapsto$ `heckeGen (𝓞 K) K v`, and the adelic measure conditioned on the adelic box `adelicBox K`; its measure on $\mathrm{GL}_2(\mathbb A_K)$ is the Haar measure `adelicGLHaar`, and its central subgroup is all of $\mathbb A_K^\times$, so that $\xi_K$ is a character of it.
--
--   **The cuspidal frame.** A type $\iota$, functions $b:\iota\to(\mathrm{GL}_2(\mathbb A_K)\to\mathbb C)$ and $\mathrm{cls}:\iota\to$ `HeckeEigensystem K ℂ` (a level, a proof that it is nonzero, and systems $a_v,b_v$ of complex eigenvalues), subject to five hypotheses. `hb`: for each $i$, $\mathrm{cls}(i)$ is a cusp class for $(P,\xi_K,N,S_K)$ — its level is $N$, its $a_v$ and $b_v$ vanish for $v\in S_K$, and its isotypic cusp submodule is nonzero — and $b_i$ lies in the intersection of that isotypic cusp submodule (the span of the smooth cuspidal automorphic, continuous, $U(N)$-right-invariant functions which are Hecke eigenfunctions with eigenvalues $a_v$ outside $S_K$ and central eigenfunctions with eigenvalues $b_v$ outside $S_K$) with the archimedean cut submodule `archCutSubmodule K tysK`, the infimum over infinite places $w$ of the supremum of the type submodules of the chosen representations at $w$. `hbn` and `hbo`: the $b_i$ are orthonormal over the canonical truncation domain with respect to `adelicGLHaar`, that is $\int b_i\overline{b_i}=1$ and $\int b_i\overline{b_j}=0$ for $i\ne j$. `hbs`: for every cusp class $\pi$ the fibre $\{i\mid \mathrm{cls}(i)=\pi\}$ is finite and the $\mathbb C$-span of $b$ over that fibre is exactly the $\pi$-isotypic cusp submodule intersected with the archimedean cut submodule. `hbc` (completeness): any $\varphi$ which is smooth cuspidal automorphic for $(P,\xi_K)$, continuous, invariant under right translation by $P.U(N)$, lies in the archimedean cut submodule and is orthogonal to every $b_i$ over the truncation domain, vanishes almost everywhere on the truncation domain.
--
--   **The family of character pairs.** A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb A_K^\times,\mathbb C^\times)$, with hypotheses: each $\mu_e,\nu_e$ is unitary (absolute value $1$ everywhere) and an idele class character (trivial on the image of $K^\times$); each is continuous; $\mu_e\nu_e=\xi_K$ for all $e$; and `_hdist`, separation: for $e\ne e'$ there is a norm-one idele (an element of the kernel of the module character) at which $\mu_e\ne\mu_{e'}$ or $\nu_e\ne\nu_{e'}$.
--
--   **The family of sections.** Numbers $n_E:\iota_E\to\mathbb N$ and functions $\varphi_{e,j}:\mathbb C\times\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ for $j\in\mathrm{Fin}(n_E(e))$, subject to the following hypotheses. Each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair `etaFst (μ e) αm hαm s` $=\mu_e\cdot\alpha_m^{\,s+1/2}$ and `etaSnd (ν e) αm hαm s` $=\nu_e\cdot\alpha_m^{-(s+1/2)}$, i.e. $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $\mathbf K$-finite at every infinite place; it is $\mathbf K_f$-smooth (a smooth vector for the finite adelic subgroup); the map $(s,g)\mapsto\varphi_{e,j}(s,g)$ is continuous; $s\mapsto\varphi_{e,j}(s,g)$ is entire; `_hφEKu` provides, at each infinite place $w$, one finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup containing all the right-translate functions $k\mapsto\varphi_{e,j}(s,gk)$, uniformly in $s$ and $g$; `_hφEflat` (flatness): on the adelic maximal compact subgroup $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$; `_hφElev`: right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; `_hφEty`: each $\varphi_{e,j}(s,\cdot)$ lies in the archimedean cut submodule; `_hφEon`: the restrictions $\varphi_{e,i}(0,\cdot)$ are orthonormal on the adelic maximal compact subgroup for `maximalCompactHaar`, $\int_{\mathbf K}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$; `_hφEspan` (completeness on the unitary axis): for every $e$, every real $t$ and every $\varphi_0$ which is an induced section for the pair attached to $(\mu_e,\nu_e)$ at $s=it$, continuous, archimedean $\mathbf K$-finite, right invariant under the above level subgroup and of the prescribed archimedean types, $\varphi_0$ lies in the span of the $\varphi_{e,j}(it,\cdot)$; and `_hpairs` (exhaustiveness): for any pair $(\mu',\nu')$ of continuous unitary idele class characters with $\mu'\nu'=\xi_K$, any real $t$ and any nonzero $\varphi_0$ admissible for that pair at $s=it$ in the same sense, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on all norm-one ideles.
--
--   **The continuation data.** Sets $O_E(e,j)\subseteq\mathbb C$ and functions $E_{e,j},N_{e,j}:\mathbb C\times\mathrm{GL}_2(\mathbb A_K)\to\mathbb C$ such that `_hEE` holds for every $(e,j)$: $O_E(e,j)$ is open, preconnected, contains the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are jointly continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb A_K)$; and for $\mathrm{Re}\,s>1/2$ one has the Eisenstein expansion
--   $$E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}\bigl(s,\;w\,u(\xi)\,g\bigr),$$
--   with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent with entry $\xi$, and the intertwining formula $N_{e,j}(s,g)=\int_{\mathbb A_K}\varphi_{e,j}(s,\,w^{-1}u(x)g)\,dx$ for the additive adelic Haar measure.
--
--   **The swap hypothesis.** Indices $e,\bar e\in\iota_E$ and a real $\sigma$ with $\mu_{\bar e}=\nu_e\cdot\|\cdot\|^{i\sigma}$ and $\nu_{\bar e}=\mu_e\cdot\|\cdot\|^{-i\sigma}$, where $\|\cdot\|^{i\sigma}$ is [`NumberField.TateGlobal.normPowChar K σ`](def/NumberField_NormPowChar.html#L22), the character sending an idele to its idele norm raised to the power $i\sigma$.
--
--   **Conclusion.** For every $j\in\mathrm{Fin}(n_E(e))$, every real $t$ and every $g\in\mathrm{GL}_2(\mathbb A_K)$, writing $s=it$ and $s'=-i(t+\sigma)$ and $v=\mathrm{vol}(\mathrm{adelicBox}\,K)$ for the real volume of the adelic box under the additive adelic Haar measure,
--   $$E_{e,j}(s,g)=\sum_{j'\in\mathrm{Fin}(n_E(\bar e))}\Bigl(\int_{\mathbf K}\bigl(v^{-1}N_{e,j}(s,k)\bigr)\,\overline{\varphi_{\bar e,j'}(s',k)}\;dk\Bigr)\,E_{\bar e,j'}(s',g),$$
--   the integral being over the adelic maximal compact subgroup against `maximalCompactHaar K`, and the sum being the finite sum over the index set of the $\bar e$-family.
--
--   This is the functional equation $E(s;\varphi)=E(-s;v^{-1}M(s)\varphi)$ of the $\mathrm{GL}_2$ Eisenstein series, restricted to the unitary axis $s=it$ and expressed in the coordinates of the fixed orthonormal frame of flat sections: the normalised intertwining image $v^{-1}N_{e,j}(it)$ is expanded against the frame $\varphi_{\bar e,\bullet}(s')$ of the swapped character pair. It feeds the continuous part of the spectral expansion over the truncation domain and is used in the pairing identities for pseudo-Eisenstein series that occur there.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar.lean

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
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.axis_continuation_eq_sum_inner_weylIntertwining_mul_axis_continuation_of_swap_normPowChar
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (e ē : ιE) (σ : ℝ)
      (_hsw : μ ē = ν e * NumberField.TateGlobal.normPowChar K σ ∧
        ν ē = μ e * (NumberField.TateGlobal.normPowChar K σ)⁻¹)
      (j : Fin (nE e)) (t : ℝ) (g : AdelicGL2 (𝓞 K) K),
    EE e j ((t : ℂ) * Complex.I) g =
      ∑ j' : Fin (nE ē),
        (∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
              NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
            conj (φE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          EE ē j' (-((((t + σ : ℝ) : ℂ)) * Complex.I)) g := by sorry
