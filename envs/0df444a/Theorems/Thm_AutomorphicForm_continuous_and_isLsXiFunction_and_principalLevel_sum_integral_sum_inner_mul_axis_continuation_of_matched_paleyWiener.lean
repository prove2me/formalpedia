-- Prove2me | Theorems.Thm_AutomorphicForm_continuous_and_isLsXiFunction_and_principalLevel_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- name    : AutomorphicForm.continuous_and_isLsXiFunction_and_principalLevel_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.363847+00:00
-- url     : https://prove2.me/theorems/a0739e12-428c-5851-b6dc-0e9b58970092
-- title:
--   Continuity, automorphy and level of a matched Eisenstein wave packet
-- statement:
--   Throughout, $K$ is a number field, with $\mathcal{O}_K$ its ring of integers, $\mathbb{A}_K$ its adele ring and $\mathrm{GL}_2(\mathbb{A}_K)$ written `AdelicGL2 (𝓞 K) K`.
--
--   **Frame data.** Real numbers $\alpha,\beta$ with $0<\alpha$ and $\alpha<\beta$; a set $\Phi_K$ of adelic matrices, which occurs in no hypothesis and in no conjunct of the conclusion; reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$ and $0<d_{1K}<d_{2K}$ and a finite set $T_K\subseteq\mathrm{GL}_2(\mathbb{A}_K)$ such that the union $\bigcup_{x\in T_K}(\,\cdot\,x)$-translates of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ whose finite part lies in $\mathrm{GL}_2$ of the integral finite adeles, whose local heights at all infinite places are $\ge c_K$, whose $x$-windows satisfy $\mathrm{xWindowSq}\le u_K^2$, and whose archimedean determinant norms lie in $[d_{1K},d_{2K}]$) satisfies `CoversModCentre`: every $g\in\mathrm{GL}_2(\mathbb{A}_K)$ can be written $\gamma g z$ in that union with $\gamma\in\mathrm{GL}_2(K)$ and $z$ a central idele scalar. A Haar measure $\nu_{ZK}$ on the idele units $\mathbb{A}_K^\times$ (for a measurable-space and Borel structure on $\mathbb{A}_K^\times$) and a set $\Omega_K$ which by $h\Omega_K$ is a fundamental domain for the image of $K^\times$ in $\mathbb{A}_K^\times$ with respect to $\nu_{ZK}$. A finite set $S_K$ of finite places, a character $\xi_K$ of the full subgroup $\top\le\mathbb{A}_K^\times$ with values in $\mathbb{C}^\times$, continuous ($h\xi_c$), trivial on the principal ideles ($h\xi_t$) and unitary, $\|\xi_K(z)\|=1$ for all $z$ ($h\xi_u$). An ideal $N\subseteq\mathcal{O}_K$ with $hN$: every finite place $v$ with $v\mid N$ belongs to $S_K$. An archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place a finite list of representations of the row-isometry subgroup, cutting out the submodule `archCutSubmodule K tysK`.
--
--   Here $\alpha_m$ denotes the monoid homomorphism $\mathbb{A}_K^\times\to\mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ via $\mathbb{R}_{\ge0}\to\mathbb{R}$, the adeles carry their Borel structure, and $h_{\alpha m}$ asserts $\alpha_m(x)>0$ for all $x$. For a character $\chi$ and $s\in\mathbb{C}$, `etaFst χ αm hαm s` $=\chi\cdot\alpha_m^{\,s+1/2}$ and `etaSnd χ αm hαm s` $=\chi\cdot\alpha_m^{-(s+1/2)}$; `IsInducedSection` for a pair $(\eta_1,\eta_2)$ says $\varphi(bg)=\eta_1(b_{11})\eta_2(b_{22})\varphi(g)$ for all adelic upper-triangular $b$ and all $g$.
--
--   **The continuous spectral family.** A countable index type $\iota_E$, characters $\mu,\nu:\iota_E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ with: each $\mu e,\nu e$ unitary ($\|\cdot\|\equiv1$) and trivial on principal ideles, each continuous, $\mu e(z)\,\nu e(z)=\xi_K(z)$ for all $z$, and ($\_hdist$) distinct indices separated already on the norm-one ideles $\ker(\mathrm{distribHaarChar})$. Integers $n_E(e)$ and functions $\varphi_E(e,j,s,\cdot)$ for $j\in\mathrm{Fin}(n_E e)$ subject to: $\_h\varphi_E$, each $\varphi_E(e,j,s)$ is an induced section for $(\mathrm{etaFst}(\mu e)\,s,\mathrm{etaSnd}(\nu e)\,s)$; $\_h\varphi_{EK}$, archimedean $K$-finiteness at every infinite place; $\_h\varphi_{Ef}$, smoothness as a vector for the finite-adelic subgroup $\ker(\mathrm{glArch})$; $\_h\varphi_{Ejc}$, joint continuity in $(s,g)$; $\_h\varphi_{Ehol}$, holomorphy in $s$ for each $g$; $\_h\varphi_{EKu}$, for each $(e,j)$ and each infinite place $w$ a finite-dimensional subspace of functions on the archimedean row-isometry subgroup containing all right translates $k\mapsto\varphi_E(e,j,s)(gk)$, uniformly in $s,g$; $\_h\varphi_{Eflat}$, flatness $\varphi_E(e,j,s)(k)=\varphi_E(e,j,0)(k)$ for $k$ in the maximal compact subgroup `adelicMaximalCompact K`; $\_h\varphi_{Elev}$, right invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; $\_h\varphi_{Ety}$, membership in `archCutSubmodule K tysK`; $\_h\varphi_{Eon}$, orthonormality $\int_{\mathbf{K}}\varphi_E(e,i,0)\overline{\varphi_E(e,j,0)}\,d(\mathrm{maximalCompactHaar}\,K)=\delta_{ij}$; $\_h\varphi_{Espan}$, completeness on the unitary axis: for every $e$, $t\in\mathbb{R}$ and every $\varphi_0$ which is an induced section for the pair at $s=it$, continuous, archimedean $K$-finite, right invariant under the above level group and of the prescribed archimedean type, $\varphi_0$ lies in the complex span of the $\varphi_E(e,j,it)$; and $\_hpairs$, exhaustiveness: for every pair $(\mu',\nu')$ of continuous unitary characters trivial on principal ideles with $\mu'\nu'=\xi_K$ and every nonzero $\varphi_0$ with the same list of properties at some $s=it$, there is $e\in\iota_E$ with $\mu e=\mu'$ and $\nu e=\nu'$ on the norm-one ideles.
--
--   **Axis continuations.** Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j,s,\cdot),N_E(e,j,s,\cdot)$ such that $\_hEE$ holds for every $(e,j)$: $O_E(e,j)$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous on $O_E(e,j)\times\mathrm{GL}_2(\mathbb{A}_K)$ jointly; and on $\{\mathrm{Re}\,s>1/2\}$ they agree with the Bruhat expansion of the Eisenstein series, $E_E(e,j,s,g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)\bigl(w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix $\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$, and with the Weyl intertwining integral $N_E(e,j,s,g)=\int_{\mathbb{A}_K}\varphi_E(e,j,s)(w^{-1}u(x)g)\,dx$ for the additive adelic Haar measure.
--
--   **The Paley–Wiener datum.** A finite index type $\iota_P$, characters $\mu_P,\nu_P:\iota_P\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$, each unitary, trivial on principal ideles and continuous, with $\mu_P e(z)\nu_P e(z)=\xi_K(z)$ for $z$ in the group $Z$ of the carrier pins `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, whose $Z$ field is the full group $\top\le\mathbb{A}_K^\times$; a map $r_P:\iota_P\to\iota_P$ with $\mu_P(r_Pe)=\nu_Pe$ and $\nu_P(r_Pe)=\mu_Pe$; and separation of distinct indices on the norm-one ideles. Functions $\psi_f(e,s,\cdot)$ which are induced sections for $(\mathrm{etaFst}(\mu_Pe)\,s,\mathrm{etaSnd}(\nu_Pe)\,s)$, jointly continuous in $(s,g)$, holomorphic in $s$, archimedean $K$-finite, smooth for the finite-adelic subgroup, with the uniform finite-dimensional $K$-type condition $\_h\psi_{Ku}$, and satisfying the vertical-strip decay $\_h\psi_{dec}$: for every $e$, $n\in\mathbb{N}$, $\sigma_0\in\mathbb{R}$ and compact $C$ there is an integrable, bounded-above $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\|\psi_f(e,\sigma'+it)(g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, $t\in\mathbb{R}$ and $g\in C$.
--
--   A function $\psi:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a slab profile for $Z=\top$ and $\xi_K$ ($\_h\psi$): measurable, invariant under left translation by unipotent matrices $u(x)$, invariant under left translation by the rational Borel subgroup, transforming by $\xi_K(z)$ under the central scalar $z$, bounded on each determinant-idele-norm slab $[d_1,d_2]$ with $d_1>0$, and supported in a height band $\mathrm{adelicHeight}\in[a,b]$ with $a>0$; and ($\_h\psi_{rep}$) represented for every $\sigma'\in\mathbb{R}$ and every $g$ by $\psi(g)=\sum_{e\in\iota_P}(4\pi)^{-1}\int_{\mathbb{R}}\psi_f(e,\sigma'+it)(g)\,dt$. Finally a matching $em:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ with $\_hem$: $\mu_P i=\mu(em\,i)\cdot\|\cdot\|^{i\tau_i}$ and $\nu_P i=\nu(em\,i)\cdot\|\cdot\|^{-i\tau_i}$ in the notation `normPowChar`, together with $\_h\psi_{lev}$, right invariance of each $\psi_f(i,s)$ under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and $\_h\psi_{ty}$, membership of each $\psi_f(i,s)$ in `archCutSubmodule K tysK`.
--
--   **Conclusion.** Put, for $g\in\mathrm{GL}_2(\mathbb{A}_K)$,
--   $$P(g)=\sum_{i\in\iota_P}\int_{\mathbb{R}}\ \sum_{j\in\mathrm{Fin}(n_E(em\,i))}\Bigl(\int_{\mathbf{K}}\psi_f(i,it)(k)\,\overline{\varphi_E(em\,i,j,i(t+\tau_i))(k)}\,d(\mathrm{maximalCompactHaar}\,K)\Bigr)\,E_E(em\,i,j,i(t+\tau_i))(g)\ dt .$$
--   Then three assertions hold: first, $P$ is continuous; second, $P$ is an $L_\xi$-function for the pins group $Z=\top$ and the character $\xi_K$, i.e. $P(\gamma g)=P(g)$ for all $\gamma\in\mathrm{GL}_2(K)$ embedded adelically and $P(zI\cdot g)=\xi_K(z)P(g)$ for all ideles $z$; third, $P(gu)=P(g)$ for all $g$ and all $u$ in the level group attached to $N$ by those pins, namely `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`.
--
--   The function $P$ is the one-term Eisenstein wave packet built from a matched Paley–Wiener datum: the packet integrates the axis continuations $E_E$ of the degenerate principal series Eisenstein series against the $\mathbf{K}$-inner products of the datum with the flat orthonormal sections. The statement records the automorphy half of the assertion that $P$ belongs to the relevant space of automorphic functions — continuity, left $\mathrm{GL}_2(K)$-invariance with central character $\xi_K$, and right invariance under the principal level group attached to $N$ — square-integrability being treated separately. It is used by the refinement that adds smoothness for the finite-adelic subgroup and membership in the prescribed archimedean type submodule.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_continuous_and_isLsXiFunction_and_principalLevel_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.continuous_and_isLsXiFunction_and_principalLevel_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener
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
    Continuous P ∧
      IsLsXiFunction (𝓞 K) K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK P ∧
      (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, P (g * u) = P g) := by sorry
