-- Prove2me | Theorems.Thm_AutomorphicForm_integral_maximalCompact_mul_sum_integral_sum_inner_mul_axis_continuation_eq_self_of_levelTypeAverage_eq_self
-- name    : AutomorphicForm.integral_maximalCompact_mul_sum_integral_sum_inner_mul_axis_continuation_eq_self_of_levelTypeAverage_eq_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/d66454c9-aacd-56c1-9b0c-4e59290ed789
-- title:
--   Averaging kernel of level and type fixes the Eisenstein packet
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}_K$ its adele ring, $G=\mathrm{GL}_2(\mathbb{A}_K)$ (`AdelicGL2 (𝓞 K) K`), and $\mathbb{K}=$ `adelicMaximalCompact K` the subgroup of those $g\in G$ whose finite part lies in `finiteIntegralGL2` and whose component at every infinite place $w$ is a row isometry; `maximalCompactHaar K` is the Haar measure on $\mathbb{K}$. The character $\alpha_m$ introduced by the `let` is the module character of $\mathbb{A}_K$, namely `distribHaarChar (AdeleRing (𝓞 K) K)` read in $\mathbb{R}^\times$ through $\mathbb{R}_{\ge 0}\to\mathbb{R}$, and `hαm` asserts that its values are positive; for a character $\chi$ of the ideles, `etaFst χ αm hαm s` $=\chi\cdot\alpha_m^{\,s+1/2}$ and `etaSnd χ αm hαm s` $=\chi\cdot\alpha_m^{-(s+1/2)}$. The predicate `IsInducedSection (𝓞 K) K χ₁ χ₂ φ` says that $\varphi(bg)=\chi_1(b_{00})\chi_2(b_{11})\varphi(g)$ for all $g\in G$ and all $b$ in the adelic Borel subgroup (lower left entry zero); `IsArchKFinite K φ` says that at each infinite place $w$ the right translates of $\varphi$ under `archRowIsometrySubgroup K w` span a finite-dimensional space; `IsKfSmooth K φ` says that $\varphi$ is a smooth vector for the finite adelic subgroup $\ker(\mathrm{gl\,Arch})$; `archCutSubmodule K tysK` is the intersection over the infinite places $w$ of the sums of the archimedean type submodules attached to the representations `tysK.rep w i`.
--
--   Frame data. Reals $\alpha<\beta$ with $0<\alpha$ (`hα`, `hαβ`); a set $\Phi_K\subseteq G$, which occurs in no further hypothesis and in no conclusion; Siegel parameters $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ (`hcK`, `hd₁K`, `hdK`) and a finite set $T_K\subseteq G$ such that (`hcovK`) the union of the right translates $\{y x : y\in\,$`centreCutSiegelSet K cK uK d₁K d₂K`$\}$ over $x\in T_K$ covers $G$ modulo global points and the centre, i.e. for each $g\in G$ there are $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\,z$ in that union (the centre-cut Siegel set consisting of the $g$ with integral finite part, local height $\ge c_K$ and window $x$-square $\le u_K^2$ at every infinite place, and archimedean determinant norm in $[d_{1K},d_{2K}]$ at every infinite place); a Haar measure $\nu_{ZK}$ on $\mathbb{A}_K^\times$ and a set $\Omega_K$ which (`hΩK`) is a fundamental domain for the group of principal ideles, the range of $K^\times\to\mathbb{A}_K^\times$, with respect to $\nu_{ZK}$; a finite set $S_K$ of finite places; a character $\xi_K$ of the full idele group (the top subgroup) with values in $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on principal ideles (`hξt`) and unitary, $|\xi_K(z)|=1$ for all $z$ (`hξu`); an ideal $N\subseteq\mathcal{O}_K$ such that every finite place dividing $N$ lies in $S_K$ (`hN`); and an archimedean type family `tysK`.
--
--   The Eisenstein family. A countable index type $\iota_E$ and characters $\mu_e,\nu_e$ of $\mathbb{A}_K^\times$ which are unitary, trivial on $K^\times$, continuous, satisfy $\mu_e\nu_e=\xi_K$ pointwise, and are separated by norm-one ideles: for $e\ne e'$ there is $z$ in [`NumberField.TateGlobal.normOneIdeles K`](def/NumberField_TateGlobalZeta.html#L16) with $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$ (`_hdist`). Integers $n_E(e)$ and functions $\varphi_{e,j}(s,\cdot)$ on $G$, $j\in\mathrm{Fin}(n_E(e))$, subject to: the induced-section law for the pair `etaFst (μ e) αm hαm s`, `etaSnd (ν e) αm hαm s` at every $s$; archimedean $K$-finiteness and $K_f$-smoothness at every $s$; joint continuity in $(s,g)$; holomorphy in $s$ for each fixed $g$; a uniform archimedean $K$-finiteness (`_hφEKu`): for each $e,j$ and each infinite place $w$ a single finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K w` containing all restrictions $k\mapsto\varphi_{e,j}(s,gk)$; flatness on the maximal compact (`_hφEflat`): $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ for $k\in\mathbb{K}$; right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`); membership in `archCutSubmodule K tysK` at every $s$ (`_hφEty`); orthonormality on $\mathbb{K}$ (`_hφEon`): $\int_{\mathbb{K}}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,dk=\delta_{ij}$; spanning (`_hφEspan`): for each $e$ and each real $t$, any $\varphi_0$ which is an induced section for the pair at $s=it$, continuous, archimedean $K$-finite, invariant under the above level subgroup and in `archCutSubmodule K tysK` lies in the $\mathbb{C}$-span of the $\varphi_{e,j}(it,\cdot)$; and exhaustiveness of the index set (`_hpairs`): for any unitary continuous characters $\mu',\nu'$ trivial on $K^\times$ with $\mu'\nu'=\xi_K$, any real $t$ and any nonzero $\varphi_0$ satisfying the same five conditions at $s=it$, there is $e\in\iota_E$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on all norm-one ideles. Finally sets $O_{e,j}\subseteq\mathbb{C}$ and functions $E_{e,j}$, $N_{e,j}$ subject to the axis-continuation package `_hEE`: $O_{e,j}$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ both $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both are continuous on $O_{e,j}\times G$; and for $\mathrm{Re}\,s>1/2$ one has the Bruhat expansions $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in K}\varphi_{e,j}(s,\,w\,u(\xi)\,g)$ with $w=$ `adelicWeyl` and $u(\xi)=$ `unipotentGL2` of the image of $\xi$, and $N_{e,j}(s,g)=$ `weylIntertwiningIntegral` of $\varphi_{e,j}(s,\cdot)$ at $g$ for the adelic additive Haar measure.
--
--   The Paley–Wiener datum. A finite index type $\iota_P$ and characters $\mu_{P,e},\nu_{P,e}$ of $\mathbb{A}_K^\times$, unitary, trivial on $K^\times$, both continuous, with $\mu_{P,e}(z)\nu_{P,e}(z)=\xi_K(z)$ for $z$ in the central subgroup of the pin package `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, that subgroup being the whole idele unit group; a map $r_P:\iota_P\to\iota_P$ interchanging the two characters, $\mu_{P,r_P(e)}=\nu_{P,e}$ and $\nu_{P,r_P(e)}=\mu_{P,e}$ (`_hr`); and separation of indices by norm-one ideles (`_hdist`). Sections $\psi_{e}(s,\cdot)$ satisfying the induced-section law for `etaFst (μP e) αm hαm s`, `etaSnd (νP e) αm hαm s`, joint continuity, holomorphy in $s$, archimedean $K$-finiteness, $K_f$-smoothness, the uniform archimedean $K$-finiteness of `_hψKu`, and the vertical-strip decay `_hψdec`: for every $e$, every $n\in\mathbb{N}$, every $\sigma_0\in\mathbb{R}$ and every compact $C\subseteq G$ there is an integrable, bounded above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_e(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function $\psi$ on $G$ which is a slab profile for the same central subgroup and $\xi_K$ (`_hψ`: measurable, invariant under left multiplication by unipotents and by global Borel points, transforming by $\xi_K$ under the central scalars, bounded on each slab $\{\,\|\det g\|\in[d_1,d_2]\,\}$ with $d_1>0$, and with adelic height confined to a band $[a,b]$, $a>0$, on the support), together with the contour representation `_hψrep`: for every $\sigma'\in\mathbb{R}$ and every $g$, $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_e(\sigma'+it,g)\,dt$. Matching data $\mathrm{em}:\iota_P\to\iota_E$ and $\tau:\iota_P\to\mathbb{R}$ with (`_hem`) $\mu_{P,i}=\mu_{\mathrm{em}(i)}\cdot\|\cdot\|^{\,i\tau_i}$ and $\nu_{P,i}=\nu_{\mathrm{em}(i)}\cdot\|\cdot\|^{-i\tau_i}$ in terms of [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22); and finally right invariance of each $\psi_i(s,\cdot)$ under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hψlev`) and membership of each $\psi_i(s,\cdot)$ in `archCutSubmodule K tysK` (`_hψty`).
--
--   The wave packet $P$ introduced by the second `let` is
--   $$P(g)=\sum_{i\in\iota_P}\int_{\mathbb{R}}\sum_{j\in\mathrm{Fin}(n_E(\mathrm{em}(i)))}\Big(\int_{\mathbb{K}}\psi_i(it,k)\,\overline{\varphi_{\mathrm{em}(i),j}(i(t+\tau_i),k)}\,dk\Big)\,E_{\mathrm{em}(i),j}\big(i(t+\tau_i),g\big)\,dt,$$
--   the inner integral being taken against `maximalCompactHaar K`.
--
--   Conclusion. For every continuous $\kappa:\mathbb{K}\to\mathbb{C}$ with the property that right averaging against $\kappa$ fixes each member of the relevant class of functions — that is, for every $\varphi:G\to\mathbb{C}$ which is continuous, archimedean $K$-finite, right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, a member of `archCutSubmodule K tysK`, and satisfies $\varphi(g\cdot z)=\xi_K(z)\varphi(g)$ for all ideles $z$ (with $z$ embedded by `centralScalar`) and all $g$, one has $\big(g\mapsto\int_{\mathbb{K}}\kappa(k)\varphi(gk)\,dk\big)=\varphi$ — the same averaging fixes the packet pointwise:
--   $$\int_{\mathbb{K}}\kappa(k)\,P(gk)\,dk=P(g)\qquad\text{for every } g\in G,$$
--   the integral again being against `maximalCompactHaar K`.
--
--   This is the statement that a wave packet assembled from the analytically continued Bruhat–Eisenstein series attached to a matched Paley–Wiener datum of level $N$ and prescribed archimedean types is fixed by any averaging kernel on the adelic maximal compact subgroup that fixes the whole class of continuous, archimedean $K$-finite, level-$N$, type-cut functions with central character $\xi_K$. It is used in the assembly of the analytic properties of this packet, by [`AutomorphicForm.continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.continuous_and_isLsXiFunction_and_isKfSmooth_and_principalLevel_and_mem_archCutSubmodule_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_maximalCompact_mul_sum_integral_sum_inner_mul_axis_continuation_eq_self_of_levelTypeAverage_eq_self.lean

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

theorem AutomorphicForm.integral_maximalCompact_mul_sum_integral_sum_inner_mul_axis_continuation_eq_self_of_levelTypeAverage_eq_self
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
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK),
    let P : AdelicGL2 (𝓞 K) K → ℂ := fun g =>
        ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
          (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
          EE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g
    ∀ (κ : ↥(adelicMaximalCompact K) → ℂ), Continuous κ →
      (∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ → IsArchKFinite K φ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ (g * u) = φ g) →
        φ ∈ archCutSubmodule K tysK →
        (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
          φ (g * centralScalar (𝓞 K) K z) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ g) →
        (fun g => ∫ k, κ k * φ (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = φ) →
      ∀ g : AdelicGL2 (𝓞 K) K, (∫ k, κ k * P (g * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) = P g := by sorry
