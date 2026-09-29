-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
-- name    : AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/17a684b7-8529-5f5e-ae13-dc92387e31ae
-- title:
--   Square-integrability of the truncated Eisenstein constant-term packet
-- statement:
--   Throughout, $K$ is a number field, and the ambient carrier data are packaged as the `CarrierPins` structure $\mathrm{pins} =$ `productionPinsOf K` applied to the canonical truncation domain $\Phi_0 =$ [`AutomorphicForm.canonicalTruncationDomain K α β`](def/AutomorphicForm_CanonicalTruncationDomain.html#L32), to the level map $M \mapsto$ `principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K`, to the Hecke generators $v \mapsto$ `heckeGen (𝓞 K) K v`, and to the box `adelicBox K`; this means: the Borel $\sigma$-algebra and the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` on $\mathrm{GL}_2$ of the adeles, the domain $\Phi_0$, centre subgroup $Z = \top$ (the full group of idele units), those level subgroups and Hecke generators, and on the adele ring the Borel $\sigma$-algebra together with the additive Haar measure conditioned on `adelicBox K`.
--
--   Geometric and measure-theoretic data. Reals $\alpha, \beta$ with $0 < \alpha$ (`hα`) and $\alpha < \beta$ (`hαβ`); a set $\Phi_K$ of adelic $\mathrm{GL}_2$ elements; reals $c_K, u_K, d_{1K}, d_{2K}$ with $0 < c_K$ (`hcK`), $0 < d_{1K}$ (`hd₁K`), $d_{1K} < d_{2K}$ (`hdK`); a finite set $T_K$ of adelic matrices; and `hcovK`, which asserts that the union over $x \in T_K$ of the right translates by $x$ of the centre-cut Siegel set `centreCutSiegelSet K cK uK d₁K d₂K` (those $g$ whose finite part is integral, whose local height at each infinite place is at least $c_K$, whose window quantity `xWindowSq` at each infinite place is at most $u_K^2$, and whose archimedean determinant norms all lie in $[d_{1K}, d_{2K}]$) covers $\mathrm{GL}_2$ of the adeles modulo left multiplication by global points and right multiplication by central ideles. Further, a Haar measure $\nu_{ZK}$ on the idele units, together with a set $\Omega_K$ and `hΩK` asserting that $\Omega_K$ is a fundamental domain for the image of $K^\times$ in the idele units acting on the idele units with respect to $\nu_{ZK}$.
--
--   Character, level and type data. A finite set $S_K$ of finite places; a homomorphism $\xi_K$ from the top subgroup of the idele units to $\mathbb{C}^\times$, continuous as a function of the idele (`hξc`), trivial on principal ideles (`hξt`), and of modulus one at every idele (`hξu`); an ideal $N$ of $\mathcal{O}_K$ with `hN`: every finite place whose ideal divides $N$ lies in $S_K$; and an archimedean type family $\mathrm{tys}_K$, giving at each infinite place a finite list of representations of the row-isometry group, whence the submodule `archCutSubmodule K tysK`.
--
--   The modulus character $\alpha_m$ is the unit-group-valued homomorphism obtained from the distributive Haar character of the adele ring via $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and `hαm` asserts that $\alpha_m$ takes strictly positive values; for a character $\mu$ and $s \in \mathbb{C}$, `etaFst μ αm hαm s` $= \mu \cdot \alpha_m^{\,s + 1/2}$ and `etaSnd ν αm hαm s` $= \nu \cdot \alpha_m^{-(s+1/2)}$, and `IsInducedSection` for a pair of characters means $\varphi(bg) = \chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for all adelic upper-triangular $b$ and all $g$.
--
--   Cuspidal basis data. A type $\iota$, functions $b : \iota \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ and a class map $\mathrm{cls} : \iota \to$ `HeckeEigensystem K ℂ`, subject to: `hb`, each $\mathrm{cls}\,i$ lies in `cuspClasses K pins ξK N SK` (level $N$, vanishing eigenvalues at the places of $S_K$, non-zero isotypic submodule) and $b\,i$ lies in the isotypic cusp submodule of $\mathrm{cls}\,i$ intersected with `archCutSubmodule K tysK`; `hbn`, each $b\,i$ has $\int_{\Phi_0} b\,i \cdot \overline{b\,i} = 1$ against `adelicGLHaar`; `hbo`, distinct indices give vanishing such integrals; `hbs`, for every class $\pi$ in `cuspClasses` the fibre $\{i \mid \mathrm{cls}\,i = \pi\}$ is finite and the $\mathbb{C}$-span of $b$ over that fibre is exactly the isotypic cusp submodule of $\pi$ intersected with the archimedean cut submodule; and `hbc`, completeness: any $\varphi$ which is a smooth cusp automorphic function for $\mathrm{pins}$ and $\xi_K$, continuous, invariant under right multiplication by $\mathrm{pins}.U\,N$, lying in the archimedean cut submodule, and orthogonal over $\Phi_0$ to every $b\,i$, vanishes almost everywhere for `adelicGLHaar` restricted to $\Phi_0$.
--
--   Continuous-spectrum family. A countable type $\iota_E$; characters $\mu, \nu : \iota_E \to$ (idele units $\to \mathbb{C}^\times$), each of modulus one (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), with $\mu_e \nu_e = \xi_K$ pointwise (`_hμν`), and pairwise separated on the norm-one ideles (`_hdist`). Ranks $n_E : \iota_E \to \mathbb{N}$ and sections $\varphi_E$, where $\varphi_E\,e\,j\,s$ is a function on $\mathrm{GL}_2(\mathbb{A}_K)$, subject to the hypotheses (each quantified over $e$, $j$ and $s$ as stated in the Lean): induced-section property for the pair $(\mathrm{etaFst}\,\mu_e, \mathrm{etaSnd}\,\nu_e)$ at $s$ (`_hφE`), archimedean $\mathbf{K}$-finiteness (`_hφEK`), smoothness for the finite part (`_hφEf`), joint continuity in $(s,g)$ (`_hφEjc`), holomorphy in $s$ for fixed $g$ (`_hφEhol`), a uniform finite-dimensional $\mathbf{K}$-type bound at each infinite place (`_hφEKu`), flatness on the maximal compact, $\varphi_E\,e\,j\,s\,k = \varphi_E\,e\,j\,0\,k$ (`_hφEflat`), invariance under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`), membership in the archimedean cut submodule (`_hφEty`), orthonormality of the $\varphi_E\,e\,\cdot\,0$ over the maximal compact for `maximalCompactHaar K` (`_hφEon`), spanning on the imaginary axis (`_hφEspan`): every continuous, archimedean $\mathbf{K}$-finite, level-$N$-invariant induced section of archimedean type at $s = it$ lies in the span of the $\varphi_E\,e\,j\,(it)$; and exhaustiveness of the family of character pairs (`_hpairs`): for every pair $\mu', \nu'$ of unitary continuous idele class characters with product $\xi_K$ and every non-zero such section at $s = it$, there is $e$ with $\mu_e = \mu'$ and $\nu_e = \nu'$ on the norm-one ideles. Finally sets $O_E\,e\,j \subseteq \mathbb{C}$ and families $E_E, N_E$, with `_hEE` (nine clauses) asserting: $O_E\,e\,j$ is open and preconnected and contains both the imaginary axis and the half-plane $\mathrm{Re}\,s > 1/2$; for each $g$, $s \mapsto E_E\,e\,j\,s\,g$ and $s \mapsto N_E\,e\,j\,s\,g$ are analytic on a neighbourhood of $O_E\,e\,j$; both are continuous on $O_E\,e\,j \times \mathrm{univ}$ in $(s,g)$; for $\mathrm{Re}\,s > 1/2$, $E_E\,e\,j\,s\,g = \varphi_E\,e\,j\,s\,g + \sum_{\xi \in K} \varphi_E\,e\,j\,s\,(w\, u(\xi)\, g)$ with $w$ the adelic Weyl element and $u(\xi)$ the unipotent with entry $\xi$; and for $\mathrm{Re}\,s > 1/2$, $N_E\,e\,j\,s\,g$ equals the Weyl intertwining integral $\int_{\mathbb{A}_K} \varphi_E\,e\,j\,s\,(w^{-1} u(x) g)\,dx$ for the adelic additive Haar measure.
--
--   Paley–Wiener datum. A finite type $\iota_P$; characters $\mu_P, \nu_P : \iota_P \to$ (idele units $\to \mathbb{C}^\times$), of modulus one (`_hμ`, `_hν`), trivial on $K^\times$ (`_hμic`, `_hνic`), continuous (`_hμc` for $\mu_P$, `_hνc` for $\nu_P$), with $\mu_P(e)(z)\,\nu_P(e)(z) = \xi_K(z)$ for $z$ in $\mathrm{pins}.Z$ (`_hμν`); an involutive index map $r_P$ exchanging the two characters (`_hr`); and pairwise separation on the norm-one ideles (`_hdist`). Sections $\psi_f$, where $\psi_f\,e\,s$ is a function on $\mathrm{GL}_2(\mathbb{A}_K)$, subject to: the induced-section property for $(\mathrm{etaFst}\,\mu_P(e), \mathrm{etaSnd}\,\nu_P(e))$ at $s$ (`_hψf`), joint continuity (`_hψjc`), holomorphy in $s$ (`_hψhol`), archimedean $\mathbf{K}$-finiteness (`_hψK`), finite-part smoothness (`_hψsm`), a uniform finite-dimensional $\mathbf{K}$-type bound at each infinite place (`_hψKu`), level-$N$ invariance (`_hψlev`), archimedean type (`_hψty`), and vertical-strip decay (`_hψdec`): for each $e$, each $n \in \mathbb{N}$, each $\sigma_0$ and each compact $C$ there is an integrable, bounded $m : \mathbb{R} \to \mathbb{R}$ with $(1+|t|)^n \|\psi_f\,e\,(\sigma' + it)\,g\| \le m(t)$ for all $|\sigma'| \le \sigma_0$, all $t$ and all $g \in C$. A function $\psi$ with `_hψ`: $\psi$ is a slab profile for $Z = \top$ and $\xi_K$, i.e. measurable, invariant under left multiplication by adelic unipotents and by global Borel points, transforming by $\xi_K$ under the centre, bounded on each determinant slab $\{\,\|\det g\| \in [d_1,d_2]\,\}$ with $d_1 > 0$, and supported in a band $a \le$ `adelicHeight` $\le b$ with $a > 0$; and `_hψrep`: for every $\sigma' \in \mathbb{R}$ and every $g$, $\psi(g) = \sum_{e \in \iota_P} (4\pi)^{-1} \int_{\mathbb{R}} \psi_f\,e\,(\sigma' + it)\,g \, dt$. Finally a matching $\mathrm{em} : \iota_P \to \iota_E$ and shifts $\tau : \iota_P \to \mathbb{R}$ with `_hem`: $\mu_P(i) = \mu(\mathrm{em}\,i) \cdot \|\cdot\|^{i\tau_i}$ and $\nu_P(i) = \nu(\mathrm{em}\,i) \cdot \|\cdot\|^{-i\tau_i}$, in terms of [`NumberField.TateGlobal.normPowChar K (τ i)`](def/NumberField_NormPowChar.html#L22).
--
--   Conclusion. There exists $R_0 \in \mathbb{R}$ such that for every $R \ge R_0$ the function
--   $$g \longmapsto \mathbf{1}_{\{\,\mathrm{adelicHeight}_K > e^{R}\,\}}(g) \cdot \sum_{i \in \iota_P} \int_{\mathbb{R}} \sum_{j \in \mathrm{Fin}(n_E(\mathrm{em}\,i))} c_{i,j}(t)\Bigl( \varphi_E\,(\mathrm{em}\,i)\,j\,(i(t+\tau_i))\,g + v^{-1}\, N_E\,(\mathrm{em}\,i)\,j\,(i(t+\tau_i))\,g \Bigr) dt,$$
--   where $c_{i,j}(t) = \int \psi_f\,i\,(it)(k) \, \overline{\varphi_E\,(\mathrm{em}\,i)\,j\,(i(t+\tau_i))(k)} \, d\,\mathrm{maximalCompactHaar}_K(k)$ and $v$ is the real number `((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal`, viewed in $\mathbb{C}$, and where the indicator is that of the high set [`AutomorphicForm.highSet (adelicHeight K) (Real.exp R)`](def/AutomorphicForm_TruncationOperator.html#L36) $= \{g \mid e^{R} < \mathrm{adelicHeight}_K(g)\}$, satisfies `MemLp` with exponent $2$ for the measure `adelicGLHaar (Fin 2) (𝓞 K) K` restricted to the canonical truncation domain $\Phi_0$.
--
--   This is the square-integrability statement for the constant-term part of an Eisenstein wave packet on $\mathrm{GL}_2$ over a number field: above the Siegel height the constant term of the axis-continued Eisenstein series is the sum of the flat section and the volume-normalised Weyl intertwining term, and the truncated wave packet built from these with Paley–Wiener coefficients lies in $L^2$ of the truncation domain. It feeds the comparison of the wave packet with its cuspidal projection in [`AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener`](thm.html#AutomorphicForm.memLp_two_restrict_canonicalTruncationDomain_sum_integral_sum_inner_mul_axis_continuation_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener.lean

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

theorem AutomorphicForm.exists_forall_memLp_two_indicator_highSet_sum_integral_sum_inner_mul_add_inv_vol_mul_axis_continuation_weylIntertwining_of_matched_paleyWiener
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
,
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      MemLp
        (fun g : AdelicGL2 (𝓞 K) K =>
          (AutomorphicForm.highSet (NumberField.AdelicHeight.adelicHeight K) (Real.exp R)).indicator
            (fun g : AdelicGL2 (𝓞 K) K => ∑ i : ιP, ∫ t : ℝ, ∑ j : Fin (nE (em i)),
              (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
                  ∂(maximalCompactHaar K)) *
                (φE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g +
                  ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) j ((((t + τ i : ℝ) : ℂ)) * Complex.I) g))
            g)
        2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) := by sorry
