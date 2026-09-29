-- Prove2me | Theorems.Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
-- name    : AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/aac4980e-cee6-576a-9752-bf0b1e560e53
-- title:
--   Uniform bounds and summability for adelic GL₂ Eisenstein data
-- statement:
--   Let $K$ be a number field, with $\mathbb{A}=\mathbb{A}_K$ the adele ring of $K$ and $\mathbb{A}^\times$ its unit group, the latter carrying a measurable structure which is the Borel structure of its topology.
--
--   **Ambient data.** Real numbers $\alpha<\beta$ with $0<\alpha$; a set $\Phi_K$ of elements of $\mathrm{GL}_2(\mathbb{A})$; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ and $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A})$ such that the union $\bigcup_{x\in T_K}\,(\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\ K\ c_K\ u_K\ d_{1K}\ d_{2K}\,]$ of right translates of the centre-cut Siegel set covers $\mathrm{GL}_2(\mathbb{A})$ modulo the centre and the global points, i.e. (`CoversModCentre`) every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}^\times$ with $\gamma g\,z$ in that union; here the centre-cut Siegel set consists of those $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at every infinite place has `localHeight` at least $c_K$ and `xWindowSq` at most $u_K^2$, and whose archimedean determinant norm at every infinite place lies in $[d_{1K},d_{2K}]$. Further: a Haar measure $\nu_{Z_K}$ on $\mathbb{A}^\times$ and a set $\Omega_K$ which is a fundamental domain for the subgroup of principal ideles (the range of $K^\times\to\mathbb{A}^\times$) acting on $\mathbb{A}^\times$ with respect to $\nu_{Z_K}$; a finite set $S_K$ of finite places of $K$; a character $\xi_K$ of the full subgroup $\top\le\mathbb{A}^\times$ with values in $\mathbb{C}^\times$, continuous (`hξc`) and trivial on principal ideles (`hξt`); an ideal $N\subseteq\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`); an archimedean type family $\mathrm{tys}_K$, that is, for each infinite place a finite list of representations of the row-isometry subgroup of that completion; functions $f_{a_K}$ on $\mathrm{GL}_2$ of the infinite adeles and $f_{S_K}(v)$ on $\mathrm{GL}_2(K_v)$ for each finite place $v$; and a real number $w$ with $\lVert\xi_K(z)\rVert=\lVert z\rVert^{w}$ for all $z$, where $\lVert\cdot\rVert=$ [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) is the module of $z$ (the value of `distribHaarChar`).
--
--   Write $\alpha_m:\mathbb{A}^\times\to\mathbb{R}^\times$ for the idele norm viewed as a monoid homomorphism into $\mathbb{R}^\times$, and assume (`hαm`) that $\alpha_m$ takes positive values; the adele ring carries its Borel measurable structure.
--
--   **Eisenstein data.** A countable type $\iota_E$; families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ such that each $\mu_e,\nu_e$ is unitary (`_hμ`, `_hν`: all values of modulus $1$), is an idele class character (`_hμic`, `_hνic`: trivial on the image of $K^\times$), and is continuous (`_hμc`, `_hνc`); the pinning $\mu_e(z)\nu_e(z)\lVert z\rVert^{w}=\xi_K(z)$ for all $e,z$ (`_hμν`); and separation (`_hdist`): for $e\ne e'$ there is a norm-one idele $z$ (an element of the kernel of `distribHaarChar`) with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$. Natural numbers $n_E(e)$ and functions $\varphi_E(e,j,s,\cdot)$ on $\mathrm{GL}_2(\mathbb{A})$ for $j<n_E(e)$ and $s\in\mathbb{C}$, subject to: `_hφE`, each $\varphi_E(e,j,s,\cdot)$ is an induced section for the pair of characters $\eta_1=\mu_e\,\alpha_m^{s+1/2}$ and $\eta_2=\nu_e\,\alpha_m^{-(s+1/2)}$, meaning $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for all $b$ in the adelic Borel subgroup and all $g$; `_hφEK`, archimedean $K$-finiteness at every infinite place (the right translates under the archimedean row-isometry subgroup span a finite-dimensional space); `_hφEf`, smoothness in the finite direction (the right-translation stabiliser inside the kernel of `glArch` is open); `_hφEjc`, joint continuity in $(s,g)$; `_hφEhol`, holomorphy in $s$ for each fixed $g$; `_hφEKu`, a uniform version of archimedean $K$-finiteness: for each $e,j$ and each infinite place $v$ there is a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $v$ containing $k\mapsto\varphi_E(e,j,s,gk)$ for all $s$ and $g$; `_hφEflat`, flatness, $\varphi_E(e,j,s,k)=\varphi_E(e,j,0,k)$ for every $k$ in the adelic maximal compact subgroup $\mathbf{K}$ (finite part in `finiteIntegralGL2`, archimedean components row isometries); `_hφElev`, right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, the intersection of the principal level subgroup at $N$ (the level-one subgroup at $N$ intersected with its conjugate by the Weyl element) with the kernel of `glArch`; `_hφEty`, membership in the archimedean cut submodule for $\mathrm{tys}_K$, i.e. at every infinite place $v$ the function lies in the sum of the isotypic submodules of the listed representations $\mathrm{tys}_K.\mathrm{rep}\ v\ i$; `_hφEon`, orthonormality at $s=0$ on $\mathbf{K}$ with respect to `maximalCompactHaar K`: $\int_{\mathbf{K}}\varphi_E(e,i,0,k)\overline{\varphi_E(e,j,0,k)}=\delta_{ij}$; `_hφEspan`, spanning on the unitary axis: for each $e$ and each $t\in\mathbb{R}$, any $\varphi_0$ which is an induced section for $\mu_e\alpha_m^{it+1/2}$, $\nu_e\alpha_m^{-(it+1/2)}$, is continuous, archimedean $K$-finite, invariant under the above level subgroup and of listed archimedean types, lies in the $\mathbb{C}$-span of the $\varphi_E(e,j,it,\cdot)$; and `_hpairs`, exhaustiveness of the index set: for every pair $\mu',\nu'$ of continuous unitary idele class characters with $\mu'(z)\nu'(z)\lVert z\rVert^{w}=\xi_K(z)$, every $t\in\mathbb{R}$ and every non-zero $\varphi_0$ satisfying the same five conditions for the pair $(\mu',\nu')$ at $s=it$, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   **Continuation data.** Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j,s,g)$, $N_E(e,j,s,g)$ such that (`_hEE`) each $O_E(e,j)$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re}s=0\}$ and the half-plane $\{\operatorname{Re}s>1/2\}$; for each $g$ both $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A})$ jointly; and for $\operatorname{Re}s>1/2$ one has $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\bigl(e,j,s,\,w_{\mathbb{A}}\,u(\xi)\,g\bigr)$, where $w_{\mathbb{A}}$ is the image of $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ and $u(\xi)$ the upper unipotent with entry $\xi$, and $N_E(e,j,s,g)=\int_{\mathbb{A}}\varphi_E\bigl(e,j,s,\,w_{\mathbb{A}}^{-1}u(x)g\bigr)\,dx$ against the additive Haar measure on $\mathbb{A}$. Finally (`_hdiag`) for each $e$ either $\mu_e=\nu_e$ or $\mu_e$ and $\nu_e$ differ at some norm-one idele.
--
--   **Conclusion.** There exist a natural number $D$, families $\tau^\mu,\tau^\nu:\iota_E\to(\text{infinite places})\to\mathbb{R}$, families $m^\mu,m^\nu:\iota_E\to(\text{infinite places})\to\mathbb{Z}$, natural numbers $M_0$ and $n_\rho$, a list $\rho_r$ ($r<n_\rho$) assigning to each finite place $v$ a character of $(K_v)^\times$, and a natural number $B_0$, such that:
--
--   (1) $n_E(e)\le D$ for every $e$.
--
--   (2) For every $e$, every infinite place $v$ and every $x\in(K_v)^\times$ whose embedding into $\mathbb{C}$ has positive real part and vanishing imaginary part, the archimedean local component of $\mu_e$ at $v$ (the composite of $\mu_e$ with the embedding of $(K_v)^\times$ placing $x$ at $v$ and $1$ elsewhere) equals $\lVert x\rVert^{\,i\tau^\mu_{e,v}}$, and likewise for $\nu_e$ with $\tau^\nu_{e,v}$.
--
--   (3) For every $e$, every infinite place $v$ and every $x\in(K_v)^\times$ whose embedding has modulus $1$, the archimedean local component of $\mu_e$ at $v$ equals $x^{m^\mu_{e,v}}$, and that of $\nu_e$ equals $x^{m^\nu_{e,v}}$.
--
--   (4) For every $e$ with $n_E(e)>0$ and every infinite place $v$, $|m^\mu_{e,v}|\le M_0$ and $|m^\nu_{e,v}|\le M_0$.
--
--   (5) For every $e$ with $n_E(e)>0$: the quotient character $\mu_e\nu_e^{-1}$ is unramified at every finite place $v\notin S_K$, in the sense that its local component at $v$ is trivial on all units $u$ of $K_v$ with both $u$ and $u^{-1}$ integral; and there is an index $r<n_\rho$ such that for all $v\in S_K$ and all such units $u$ the local component of $\mu_e\nu_e^{-1}$ at $v$ agrees with $\rho_r(v)$ at $u$. (Only the quotient $\mu_e\nu_e^{-1}$ is constrained here, not $\mu_e$ and $\nu_e$ separately.)
--
--   (6) For every natural number $B\ge B_0$: for each $e$ the function $t\mapsto\bigl(1+\sum_v(|t+\tau^\mu_{e,v}|+|t-\tau^\nu_{e,v}|)\bigr)^{-B}$ is integrable on $\mathbb{R}$, the sum over $e$ of $\int_{\mathbb{R}}\bigl(1+\sum_v(|t+\tau^\mu_{e,v}|+|t-\tau^\nu_{e,v}|)\bigr)^{-B}\,dt$, with the term replaced by $0$ when $n_E(e)=0$, is summable, and the sum over $e$ of $\bigl(1+\sum_v(|\tau^\mu_{e,v}|+|\tau^\nu_{e,v}|)\bigr)^{-B}$, again with the term replaced by $0$ when $n_E(e)=0$, is summable. In both sums $v$ runs over the infinite places of $K$.
--
--   This is the arithmetic bookkeeping for the index set of the continuous spectrum of $\mathrm{GL}_2$ over a number field at fixed level $N$, fixed central character $\xi_K$ and a fixed finite list of archimedean types: a level- and type-dependent bound on the number of flat sections per pair of characters, the archimedean parameters and weights of the inducing characters with a bound on the weights, a finite list exhausting the ramification of the quotient characters at the places of $S_K$, and summability of the resulting parameter profiles. It feeds the construction of a summable dominating family for the Maass–Selberg pairings along the unitary axis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
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

theorem AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
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
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
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
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
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
      (_hdiag : ∀ e : ιE, μ e = ν e ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z)
      ,
    ∃ (D : ℕ) (τμ τν : ιE → InfinitePlace K → ℝ) (mμ mν : ιE → InfinitePlace K → ℤ) (M₀ : ℕ) (nρ : ℕ)
      (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (B₀ : ℕ),
      (∀ e, nE e ≤ D) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν e v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v)) ∧
      (∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ)) ∧
      (∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e * (ν e)⁻¹) v) ∧
        ∃ r : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e * (ν e)⁻¹) v u = ρs r v u) ∧
      (∀ B : ℕ, B₀ ≤ B →
        (∀ e : ιE, MeasureTheory.Integrable
          (fun t : ℝ => (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)))) ∧
        Summable (fun e : ιE => if 0 < nE e then
          ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)) else 0) ∧
        Summable (fun e : ιE => if 0 < nE e then
          (1 + ∑ v : InfinitePlace K, (|τμ e v| + |τν e v|)) ^ (-(B : ℝ)) else 0)) := by sorry
