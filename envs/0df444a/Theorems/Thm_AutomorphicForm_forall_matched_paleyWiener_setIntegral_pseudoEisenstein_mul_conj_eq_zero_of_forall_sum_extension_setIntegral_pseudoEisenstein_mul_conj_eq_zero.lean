-- Prove2me | Theorems.Thm_AutomorphicForm_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- name    : AutomorphicForm.forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/3b7530fc-d78d-57a0-a1c6-5794cdf95f67
-- title:
--   Arbitrary-family pseudo-Eisenstein orthogonality from sum-extension orthogonality
-- statement:
--   The statement is set in a fixed wave-packet frame for $\mathrm{GL}_2$ over a number field $K$, and asserts that orthogonality of a function $f$ against the pseudo-Eisenstein series of all Paley–Wiener data carried by *enlargements* of one reference character family forces orthogonality against the pseudo-Eisenstein series of *every* finite matched Paley–Wiener datum of the prescribed level and archimedean type.
--
--   **Frame data.** $K$ is a number field; $\alpha,\beta$ are reals with $0<\alpha$ and $\alpha<\beta$; $\Phi K$ is a set of elements of $\mathrm{GL}_2(\mathbb{A}_K)$ (here written `AdelicGL2 (𝓞 K) K`); $cK,uK,d_1K,d_2K$ are reals and $TK$ a finite set of adelic matrices, subject to $0<cK$, $0<d_1K$, $d_1K<d_2K$ and the covering hypothesis `hcovK`: the union over $x\in TK$ of the right translates by $x$ of `centreCutSiegelSet K cK uK d₁K d₂K` (matrices with integral finite part, local height at least $cK$ at every infinite place, $x$-window square at most $uK^2$, and archimedean determinant norm in $[d_1K,d_2K]$) covers modulo centre and rational points: for every $g$ there are $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma\, g\, z$ (the images under `globalPoints` and `centralScalar`) in that union. A Haar measure $\nu ZK$ on the idele group is fixed, together with a set $\Omega K$ that is a fundamental domain for the image of $K^\times$ in the ideles. $SK$ is a finite set of finite places, $N$ an ideal of $\mathcal{O}_K$ with `hN`: every prime $v$ whose ideal divides $N$ lies in $SK$. The character $\xi K$ is a homomorphism from the full subgroup $\top$ of the ideles to $\mathbb{C}^\times$, continuous (`hξc`), trivial on the principal ideles (`hξt`) and of absolute value $1$ everywhere (`hξu`). Finally $\mathrm{tys}K$ is an archimedean type family, i.e. for each infinite place a finite list of representations of the row-isometry subgroup of the completion. Throughout, $\alpha m$ denotes the modulus character of the adele ring, namely the distributive Haar character composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$ and viewed as a homomorphism into $\mathbb{R}^\times$, and `hαm` records that its values are positive; the adele ring carries its Borel structure.
--
--   **The Eisenstein index family.** A countable type $\iota E$ is given with families of idele characters $\mu,\nu:\iota E\to(\mathbb{A}_K^\times\to\mathbb{C}^\times)$ such that each $\mu_e,\nu_e$ is unitary (absolute value $1$ at every idele) and trivial on the principal ideles, each is continuous, $\mu_e(z)\nu_e(z)=\xi K(z)$ for all ideles $z$, and distinct indices are separated on the norm-one ideles (the kernel of the distributive Haar character): for $e\ne e'$ some norm-one idele $z$ has $\mu_e(z)\ne\mu_{e'}(z)$ or $\nu_e(z)\ne\nu_{e'}(z)$.
--
--   For each $e$ an integer $nE_e$ and sections $\varphi E_{e,j}(s,\cdot)$, $j\in\mathrm{Fin}(nE_e)$, are given, subject to the following group of hypotheses: each $\varphi E_{e,j}(s,\cdot)$ is an induced section for the pair $\bigl(\mu_e\cdot\alpha m^{\,s+1/2},\ \nu_e\cdot\alpha m^{-(s+1/2)}\bigr)$, that is $\varphi(bg)$ equals the product of the two characters evaluated at the diagonal entries $b_{00},b_{11}$ of $b$ times $\varphi(g)$ for every $b$ in the adelic Borel subgroup (lower-left entry $0$); it is archimedean $K$-finite (at each infinite place the right translates under the row-isometry subgroup span a finite-dimensional space) and $K_f$-smooth (a smooth vector for the finite-adelic subgroup, the kernel of `glArch`); $(s,g)\mapsto\varphi E_{e,j}(s,g)$ is continuous and $s\mapsto\varphi E_{e,j}(s,g)$ is entire; at each infinite place the translates lie in one fixed finite-dimensional subspace, uniformly in $s$ and $g$; the section is flat, its value at any $s$ on the adelic maximal compact agreeing with its value at $s=0$; it is invariant under right translation by `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`; it lies in the archimedean cut submodule `archCutSubmodule K tysK`; the flat sections are orthonormal on the maximal compact, $\int \varphi E_{e,i}(0,k)\overline{\varphi E_{e,j}(0,k)}\,d(\mathrm{maximalCompactHaar}\,K)=\delta_{ij}$; the hypothesis `_hφEspan` states that every continuous, archimedean $K$-finite, level-$N$-invariant induced section of type $\mathrm{tys}K$ for the pair at $s=it$ lies in the complex span of the $\varphi E_{e,j}(it,\cdot)$; and `_hpairs` states that every pair $(\mu',\nu')$ of continuous unitary idele-class characters with $\mu'\nu'=\xi K$ admitting a nonzero continuous, archimedean $K$-finite, level-$N$-invariant induced section of type $\mathrm{tys}K$ at some point $it$ of the unitary axis agrees with some $(\mu_e,\nu_e)$ on the norm-one ideles.
--
--   Sets $OE_{e,j}\subseteq\mathbb{C}$ and functions $EE_{e,j}$, $NE_{e,j}$ are given, and `_hEE` asserts for each $(e,j)$: $OE_{e,j}$ is open and preconnected, contains the line $\mathrm{Re}\,s=0$ and the half-plane $\mathrm{Re}\,s>1/2$; for each $g$ both $s\mapsto EE_{e,j}(s,g)$ and $s\mapsto NE_{e,j}(s,g)$ are analytic on a neighbourhood of $OE_{e,j}$; both are continuous on $OE_{e,j}\times\mathrm{univ}$ in $(s,g)$; for $\mathrm{Re}\,s>1/2$ one has $EE_{e,j}(s,g)=\varphi E_{e,j}(s,g)+\sum_{\xi\in K}\varphi E_{e,j}\bigl(s,\ w\,u(\xi)\,g\bigr)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent matrix $\begin{pmatrix}1&\xi\\0&1\end{pmatrix}$; and for $\mathrm{Re}\,s>1/2$, $NE_{e,j}(s,g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K}\varphi E_{e,j}(s,\ w^{-1}u(x)g)\,dx$ against the adelic additive Haar measure.
--
--   **The reference Paley–Wiener datum.** A finite type $\iota P$ is given with character families $\mu P,\nu P$, hypotheses that the $\mu P_e$ and $\nu P_e$ are unitary, trivial on principal ideles and continuous, that $\mu P_e(z)\nu P_e(z)=\xi K(z)$ for $z$ in the central subgroup $Z$ of the record `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, which is $\top$, a map $rP:\iota P\to\iota P$ interchanging the two families ($\mu P_{rP(e)}=\nu P_e$, $\nu P_{rP(e)}=\mu P_e$), and separation of distinct indices on the norm-one ideles. A family of sections $\psi f_e(s,\cdot)$ is given, with the group of hypotheses: induced section for $\bigl(\mu P_e\,\alpha m^{s+1/2},\nu P_e\,\alpha m^{-(s+1/2)}\bigr)$, joint continuity, holomorphy in $s$, archimedean $K$-finiteness, $K_f$-smoothness, uniform finite-dimensionality of archimedean translates, and the Paley–Wiener decay `_hψdec`: for every $e$, every $n\in\mathbb{N}$, every $\sigma_0$ and every compact $C$ there is an integrable $m:\mathbb{R}\to\mathbb{R}$, bounded above, with $(1+|t|)^n\|\psi f_e(\sigma'+it,g)\|\le m(t)$ for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. A function $\psi$ is given which is a slab profile for $Z=\top$ and $\xi K$ (`IsSlabProfile`: measurable; invariant under left multiplication by adelic unipotents and by rational Borel elements; transforming by $\xi K(z)$ under the central scalar $z$; bounded on each slab where the idele norm of the determinant lies in $[d_1,d_2]$ with $d_1>0$; and supported where the adelic height lies in a fixed interval $[a,b]$ with $a>0$), with the wave-packet representation $\psi(g)=\sum_{e}(4\pi)^{-1}\int_{\mathbb{R}}\psi f_e(\sigma'+it,g)\,dt$ for every real $\sigma'$ and every $g$; matching data $em:\iota P\to\iota E$, $\tau:\iota P\to\mathbb{R}$ with $\mu P_i=\mu_{em(i)}\cdot\|\cdot\|^{i\tau(i)}$ and $\nu P_i=\nu_{em(i)}\cdot\|\cdot\|^{-i\tau(i)}$ in terms of [`NumberField.TateGlobal.normPowChar`](def/NumberField_NormPowChar.html#L22); and level-$N$ invariance and membership in `archCutSubmodule K tysK` for every $\psi f_i(s,\cdot)$.
--
--   **The orthogonality hypothesis.** A function $f$ on $\mathrm{GL}_2(\mathbb{A}_K)$ is given, and `_hsum` asserts: for every finite type $\iota X$ with character families $\mu X,\nu X$ that are unitary, trivial on principal ideles, continuous, satisfy $\mu X_e\nu X_e=\xi K$ on the central subgroup of the above pins record, are swap-closed under a map $rX$, are separated among themselves on the norm-one ideles and separated there from every $(\mu P_i,\nu P_i)$, and are matched into the Eisenstein family by data $emX,\tau X$ as above; and for every family $\psi f'$ indexed by $\iota P\oplus\iota X$ whose members are induced sections for $\bigl(\mathrm{Sum.elim}\ \mu P\ \mu X\bigr)_e$ and $\bigl(\mathrm{Sum.elim}\ \nu P\ \nu X\bigr)_e$ twisted as before, jointly continuous, holomorphic in $s$, archimedean $K$-finite, $K_f$-smooth, of uniformly finite archimedean type, and satisfying the same Paley–Wiener decay; and for every $\psi'$ which is a slab profile for $\top$ and $\xi K$ with $\psi'(g)=\sum_{e\in\iota P\oplus\iota X}(4\pi)^{-1}\int_{\mathbb{R}}\psi f'_e(\sigma'+it,g)\,dt$ for every $\sigma'$, with all $\psi f'_i(s,\cdot)$ invariant under the level-$N$ subgroup and lying in `archCutSubmodule K tysK`, one has
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta} \bigl(\mathrm{pseudoEisenstein}\,K\,\psi'\bigr)(g)\,\overline{f(g)}\ d\bigl(\mathrm{adelicGLHaar}\ (\mathrm{Fin}\,2)\,\mathcal{O}_K\,K\bigr)=0,$$
--   where $\mathrm{pseudoEisenstein}\,K\,\phi$ is the function $g\mapsto \phi(g)+\sum_{b\in K}\phi\bigl(w\,u(b)\,g\bigr)$ and the truncation domain is the one selected by `canonicalTruncationData K α β` from the slab parameters $\alpha,\beta$.
--
--   **Conclusion.** Under these hypotheses, for every finite type $\iota P_2$ equipped with character families $\mu P_2,\nu P_2$ satisfying the same conditions as the reference family (unitarity, triviality on principal ideles, continuity of both families, the product condition $\mu P_2{}_e\,\nu P_2{}_e=\xi K$ on the central subgroup of the pins record, a swap map $rP_2$, separation of distinct indices on the norm-one ideles), for every section family $\psi f_2$ satisfying the same list (induced section for the twisted pairs, joint continuity, holomorphy in $s$, archimedean $K$-finiteness, $K_f$-smoothness, uniform finite archimedean type, Paley–Wiener decay, level-$N$ invariance, membership in `archCutSubmodule K tysK`), and for every $\psi_2$ that is a slab profile for $\top$ and $\xi K$ with the wave-packet representation $\psi_2(g)=\sum_e(4\pi)^{-1}\int_{\mathbb{R}}\psi f_2{}_e(\sigma'+it,g)\,dt$ at every $\sigma'$ and matching data $em_2,\tau_2$ into the Eisenstein family as above, the single identity
--   $$\int_{\mathrm{canonicalTruncationDomain}\,K\,\alpha\,\beta} \bigl(\mathrm{pseudoEisenstein}\,K\,\psi_2\bigr)(g)\,\overline{f(g)}\ d\bigl(\mathrm{adelicGLHaar}\ (\mathrm{Fin}\,2)\,\mathcal{O}_K\,K\bigr)=0$$
--   holds. No relation between $\iota P_2$ and the reference family $\iota P$ is required.
--
--   This is the bridging step in the Paley–Wiener wave-packet part of the spectral analysis of $\mathrm{GL}_2$ over a number field: it converts orthogonality of $f$ against pseudo-Eisenstein wave packets built on enlargements of one fixed finite character family into orthogonality against wave packets built on an arbitrary finite matched family, the passage being a re-indexing of finite Paley–Wiener families. It is deduced from [`AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light`](thm.html#AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_and_sections_eq_of_matched_paleyWiener_of_matched_paleyWiener_light), which produces a common enlargement carrying both data, and is used in [`AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.exists_forall_pseudoEisenstein_sub_residualProj_ae_eq_mul_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero.lean

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

theorem AutomorphicForm.forall_matched_paleyWiener_setIntegral_pseudoEisenstein_mul_conj_eq_zero_of_forall_sum_extension_setIntegral_pseudoEisenstein_mul_conj_eq_zero
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
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (f : AdelicGL2 (𝓞 K) K → ℂ)
      (_hsum : ∀
      (ιX : Type) [Fintype ιX]
      (μX νX : ιX → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμX : ∀ e, IsUnitaryChar (𝓞 K) K (μX e)) (_hνX : ∀ e, IsUnitaryChar (𝓞 K) K (νX e))
      (_hμicX : ∀ e, IsIdeleClassChar (𝓞 K) K (μX e)) (_hνicX : ∀ e, IsIdeleClassChar (𝓞 K) K (νX e))
      (_hμcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μX e x : ℂˣ) : ℂ))
      (_hνcX : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νX e x : ℂˣ) : ℂ))
      (_hμνX : ∀ (e : ιX)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μX e (z : (AdeleRing (𝓞 K) K)ˣ) * νX e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rX : ιX → ιX) (_hrX : ∀ e, μX (rX e) = νX e ∧ νX (rX e) = μX e)
      (_hdistX : ∀ e e' : ιX, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μX e x ≠ μX e' x ∨ νX e x ≠ νX e' x)
      (_hdistPX : ∀ (i : ιP) (e : ιX), ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP i x ≠ μX e x ∨ νP i x ≠ νX e x)
      (emX : ιX → ιE) (τX : ιX → ℝ)
      (_hemX : ∀ e : ιX, μX e = μ (emX e) * NumberField.TateGlobal.normPowChar K (τX e) ∧
        νX e = ν (emX e) * (NumberField.TateGlobal.normPowChar K (τX e))⁻¹)
      (ψf' : ιP ⊕ ιX → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf' : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (Sum.elim μP μX e) αm hαm s) (etaSnd (Sum.elim νP νX e) αm hαm s) (ψf' e s))
      (_hψjc' : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf' e p.1 p.2))
      (_hψhol' : ∀ e g, Differentiable ℂ (fun s => ψf' e s g))
      (_hψK' : ∀ e s, IsArchKFinite K (ψf' e s)) (_hψsm' : ∀ e s, IsKfSmooth K (ψf' e s))
      (_hψKu' : ∀ (e : ιP ⊕ ιX) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf' e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψdec' : ∀ (e : ιP ⊕ ιX) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ' : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ' : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ')
      (_hψrep' : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ' g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf' e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψlev' : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf' i s (g * u) = ψf' i s g)
      (_hψty' : ∀ i (s : ℂ), ψf' i s ∈ archCutSubmodule K tysK),
        ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ' g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (ιP₂ : Type) [Fintype ιP₂]
      (μP₂ νP₂ : ιP₂ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₂ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₂ e)) (_hν₂ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₂ e))
      (_hμic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₂ e)) (_hνic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₂ e))
      (_hμc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₂ e x : ℂˣ) : ℂ))
      (_hμν₂ : ∀ (e : ιP₂)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₂ : ιP₂ → ιP₂) (_hr₂ : ∀ e, μP₂ (rP₂ e) = νP₂ e ∧ νP₂ (rP₂ e) = μP₂ e)
      (_hdist₂ : ∀ e e' : ιP₂, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₂ e x ≠ μP₂ e' x ∨ νP₂ e x ≠ νP₂ e' x)
      (ψf₂ : ιP₂ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₂ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₂ e) αm hαm s) (etaSnd (νP₂ e) αm hαm s) (ψf₂ e s))
      (_hψjc₂ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₂ e p.1 p.2))
      (_hψhol₂ : ∀ e g, Differentiable ℂ (fun s => ψf₂ e s g))
      (_hψK₂ : ∀ e s, IsArchKFinite K (ψf₂ e s)) (_hψsm₂ : ∀ e s, IsKfSmooth K (ψf₂ e s))
      (_hψKu₂ : ∀ (e : ιP₂) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₂ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₂ e x : ℂˣ) : ℂ))
      (_hψdec₂ : ∀ (e : ιP₂) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₂)
      (_hψrep₂ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₂ : ιP₂ → ιE) (τ₂ : ιP₂ → ℝ)
      (_hem₂ : ∀ i : ιP₂, μP₂ i = μ (em₂ i) * NumberField.TateGlobal.normPowChar K (τ₂ i) ∧
        νP₂ i = ν (em₂ i) * (NumberField.TateGlobal.normPowChar K (τ₂ i))⁻¹)
      (_hψlev₂ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₂ i s (g * u) = ψf₂ i s g)
      (_hψty₂ : ∀ i (s : ℂ), ψf₂ i s ∈ archCutSubmodule K tysK),
    ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
            AutomorphicForm.pseudoEisenstein K ψ₂ g * conj (f g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0 := by sorry
