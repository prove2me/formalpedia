-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat
-- name    : AutomorphicForm.exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/b1c162ad-3f55-567f-a269-4d1143b6c28a
-- title:
--   Uniform dilation bound for Whittaker coefficients of flat Eisenstein families
-- statement:
--   Throughout, $K$ is a number field with ring of integers $\mathcal O_K$, $\mathbb A_K$ denotes its adele ring and $\mathbb A_K^\times$ its group of ideles, equipped with the Borel structures used by the project (the adele ring carries `adeleBorel`, i.e. the Borel $\sigma$-algebra, and $\mathrm{GL}_2(\mathbb A_K)$ carries `glBorel`).
--
--   The outer data are: a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top \le \mathbb A_K^\times$ to $\mathbb C^\times$ whose associated function on ideles is continuous (`hξc`) and which is trivial on the image of $K^\times$ under $\mathrm{Units.map}$ of the structure map $K \to \mathbb A_K$ (`hξt`); an ideal $N \subseteq \mathcal O_K$ such that every finite place $v$ with $v \mid N$ lies in $S_K$ (`hN`); an archimedean type family `tysK`, which assigns to each infinite place $w$ of $K$ a number $\mathrm{card}(w)$ of types and, for each index $i < \mathrm{card}(w)$, a dimension $n$ together with a representation of `rowIsometrySubgroup₀ w.Completion` on $\mathbb C^{n}$; a real number $w$ such that $\lVert \xi_K(z)\rVert = \lVert z\rVert^{w}$ for every idele $z$ (`hξw`), where $\lVert z \rVert$ is [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the real value of the module character $\mathrm{distribHaarChar}$ of $\mathbb A_K$ at $z$; an additive character $\psi$ of $\mathbb A_K$ with values in $\mathbb C$ which is `IsGlobalAddChar`, i.e. trivial on the image of $K$, continuous, and not identically $1$; a compact set $U \subseteq \mathbb A_K^\times$; and a real $r_0 > 0$.
--
--   The statement first introduces $\alpha_m \colon \mathbb A_K^\times \to \mathbb R^\times$, the unit-valued homomorphism obtained from $\mathrm{distribHaarChar}(\mathbb A_K)$ composed with $\mathbb R_{\ge 0} \to \mathbb R$; thus $\alpha_m(x)$ is the idele norm of $x$ viewed as a unit of $\mathbb R$.
--
--   The assertion is: there exist a finite set $S$ of finite places with $S_K \subseteq S$, a natural number $k$ and a fractional ideal $I$ of $K$ such that for every $N_d \in \mathbb N$ there are a real $C > 0$ and an $A \in \mathbb N$ for which the following holds for all the inducing data described next. (Thus $S$, $k$, $I$ are chosen before $N_d$, and $C$, $A$ before the characters and the sections: the bound is uniform in them.)
--
--   The inducing data consist of: a proof `hαm` that $\alpha_m(x) > 0$ for all $x$; two homomorphisms $\mu, \nu \colon \mathbb A_K^\times \to \mathbb C^\times$ which are unitary ($\lVert\mu(x)\rVert = \lVert\nu(x)\rVert = 1$ for all $x$), are idele class characters (trivial on the image of $K^\times$), and have continuous associated complex-valued functions, and which satisfy $\mu(z)\nu(z)\lVert z\rVert^{w} = \xi_K(z)$ for every idele $z$; archimedean parameters $\tau_\mu, \tau_\nu \colon \{\text{infinite places}\} \to \mathbb R$ such that for each infinite place $v$ and each unit $x$ of $K_v$ whose embedding into $\mathbb C$ has positive real part and vanishing imaginary part one has `archLocalChar` $\mu$ at $v$ evaluated at $x$ equal to $\lVert \mathrm{archUnitHom}_v(x)\rVert^{\,\tau_\mu(v) i}$, and likewise for $\nu$ with $\tau_\nu$ (here `archLocalChar` is the composite of the character with the embedding $K_v^\times \to \mathbb A_K^\times$ supported at $v$); weights $m_\mu, m_\nu \colon \{\text{infinite places}\} \to \mathbb Z$ such that for each infinite place $v$ and each $x$ with $\lVert x \rVert = 1$ the local character of $\mu$ at $v$ is the $m_\mu(v)$-th power of the embedding of $x$, and likewise for $\nu$ with $m_\nu$; a family $\psi_f \colon \mathbb C \to \mathrm{GL}_2(\mathbb A_K) \to \mathbb C$; and a choice of uniformisers $\varpi_v \in (K_v)^\times$ at all finite places $v$, normalised by $\mathrm{val}(\varpi_v) = \mathrm{ofAdd}(-1)$.
--
--   The family $\psi_f$ is subject to the following hypotheses. For every $s$, $\psi_f(s)$ is an induced section for the pair of characters $\mu\,\alpha_m^{\,s+1/2}$ and $\nu\,\alpha_m^{-(s+1/2)}$ (`etaFst`, `etaSnd`): that is, $\psi_f(s)(bg) = \eta_1(b_{00})\,\eta_2(b_{11})\,\psi_f(s)(g)$ for all $g$ and all $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry), where $b_{00}, b_{11}$ are the diagonal entries. For every $s$, $\psi_f(s)$ is archimedean $K$-finite at each infinite place (its right translates under `archRowIsometrySubgroup` span a finite-dimensional space) and is $K_f$-smooth (its stabiliser for right translation inside `finiteAdelicGL2Subgroup`, the kernel of the archimedean projection $\mathrm{glArch}$, is open). The map $(s,g) \mapsto \psi_f(s)(g)$ is continuous, and for each $g$ the map $s \mapsto \psi_f(s)(g)$ is differentiable on $\mathbb C$. At each infinite place $v$ there is one finite-dimensional subspace $W$ of functions on `archRowIsometrySubgroup K v` containing the function $k \mapsto \psi_f(s)(gk)$ for all $s$ and all $g$ simultaneously. The family is flat: $\psi_f(s)(k) = \psi_f(0)(k)$ for every $s$ and every $k$ in `adelicMaximalCompact K`, the subgroup of elements whose finite part is integral and whose archimedean component at each infinite place is a row isometry. Each $\psi_f(s)$ is right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, where `principalLevel` is the intersection of the level-$N$ subgroup with its conjugate by the Weyl element. Each $\psi_f(s)$ lies in `archCutSubmodule K tysK`, the intersection over infinite places $w$ of the sums over $i$ of the type submodules attached to the representations `tysK.rep w i`. Finally $\int_{\mathbf K} \lVert \psi_f(0)(k)\rVert^2 \, d(\mathrm{maximalCompactHaar}) \le 1$, the integral being over the adelic maximal compact with its Haar measure.
--
--   The Bruhat-form Eisenstein series attached to the family is defined by
--   $$E(s)(h) = \psi_f(s)(h) + \sum_{\xi \in K} \psi_f(s)\bigl(w_0\, n(\xi)\, h\bigr),$$
--   where $w_0 =$ `adelicWeyl` is the image in $\mathrm{GL}_2(\mathbb A_K)$ of the antidiagonal matrix $\begin{pmatrix}0&1\\1&0\end{pmatrix}$ over $K$, $n(\xi) = \begin{pmatrix}1&\xi\\0&1\end{pmatrix}$ for $\xi$ mapped into $\mathbb A_K$, and the sum is an unconditional sum (`∑'`).
--
--   The conclusion asserts the existence of a family $\mathcal J_\xi(s,y)$, indexed by the nonzero $\xi \in K$ and depending on $s \in \mathbb C$ and on an idele $y$, with the following six properties.
--
--   (i) For each nonzero $\xi$ and each idele $y$, the function $s \mapsto \mathcal J_\xi(s,y)$ is analytic on a neighbourhood of every point of $\mathbb C$.
--
--   (ii) For each nonzero $\xi$, each $s$ with $\operatorname{Re} s > 1$ and each idele $y$,
--   $$W_\psi\bigl(E(s)\bigr)\bigl(\xi, \mathrm{diag}(y,1)\bigr) = \Bigl(\prod_{v \notin S}\bigl(1 - (\mu\nu^{-1})_v(\varpi_v)\, \mathrm{N}(v)^{-(2s+1)}\bigr)\Bigr) \cdot \mathcal J_\xi(s,y),$$
--   where the left-hand side is `whittakerCoefficient K (productionPins K) ψ (E s) ξ (diagOne y)`, namely $\int \psi_f$-type integral $\int E(s)\bigl(n(x)\,\mathrm{diag}(y,1)\bigr)\psi(-\xi x)\,d\nu(x)$ over $\mathbb A_K$ with the measure pinned by `productionPins K` (the additive adelic Haar measure conditioned on the adelic box), $(\mu\nu^{-1})_v$ is the local component `localChar` of $\mu\nu^{-1}$ at $v$, $\mathrm{N}(v) =$ `Ideal.absNorm` of the prime of $v$, the product being an unconditional product over the places not in $S$, and $\mathrm{diag}(y,1) =$ `diagOne y`.
--
--   (iii) For each nonzero $\xi$, the map $(s,y) \mapsto \mathcal J_\xi(s,y)$ is continuous.
--
--   (iv) Equivariance: for each nonzero $\xi$, each $\eta \in K^\times$, each $s$ and each idele $y$, $\mathcal J_\xi(s, \eta y) = \mathcal J_{\xi\eta}(s, y)$, where $\eta$ acts through the image of $K^\times$ in $\mathbb A_K^\times$ and $\xi\eta \ne 0$.
--
--   (v) A dilation bound on compacta, with constants depending on the data: for every compact $C_1 \subseteq \mathbb C$, every compact $U_1 \subseteq \mathbb A_K^\times$ and every $r_1 > 0$ there exist $k_1 \in \mathbb N$ and a fractional ideal $I_1$ such that for every $N_1 \in \mathbb N$ there is $c_1 \in \mathbb R$ with the following property. Let $s \in C_1$, $u \in U_1$, let $z$ be an idele and $r \ge r_1$ a real number such that the finite part of $z$ is $1$ and the component of $z$ at every infinite place embeds to the real number $r$; then for every nonzero $\xi \in K$: if $\xi \notin I_1$ then $\mathcal J_\xi(s, zu) = 0$, and
--   $$\lVert \mathcal J_\xi(s,zu)\rVert \le c_1\, r^{\,n(1/2 - \operatorname{Re} s)} \max\bigl(1, |\mathrm{N}_{K/\mathbb Q}(\xi)|\bigr)^{k_1} \prod_{w \text{ real}} \bigl(1 + r\,|\xi_w|\bigr)^{-N_1} \prod_{w \text{ complex}} \bigl(1 + r\,\lVert \xi_w\rVert\bigr)^{-2N_1},$$
--   where $n = [K:\mathbb Q]$ and $\xi_w$ denotes the component of $\xi$ at $w$ under the mixed embedding.
--
--   (vi) The uniform bound on the unitary axis, with the constants $C$, $A$, $k$, $I$ and $N_d$ fixed above: for every real $t$, every $u \in U$, every idele $z$ and every real $r \ge r_0$ such that the finite part of $z$ is $1$ and the component of $z$ at every infinite place embeds to $r$, and every nonzero $\xi \in K$: if $\xi \notin I$ then $\mathcal J_\xi(it, zu) = 0$, and
--   $$\lVert \mathcal J_\xi(it, zu)\rVert \le C \Bigl(1 + \sum_{v} \bigl(|t + \tau_\mu(v)| + |t - \tau_\nu(v)| + |m_\mu(v)| + |m_\nu(v)|\bigr)\Bigr)^{A} r^{\,n/2} \max\bigl(1, |\mathrm{N}_{K/\mathbb Q}(\xi)|\bigr)^{k} \prod_{w \text{ real}} \bigl(1 + r\,|\xi_w|\bigr)^{-N_d} \prod_{w \text{ complex}} \bigl(1 + r\,\lVert \xi_w\rVert\bigr)^{-2N_d},$$
--   the sum being over all infinite places $v$ of $K$.
--
--   This is the uniform form of the Whittaker expansion of a flat holomorphic family of $\mathrm{GL}_2$ Eisenstein series over a number field: the coefficients along the split torus $\mathrm{diag}(y,1)$ factor as an Euler product outside a finite set of places times an entire function $\mathcal J$, which satisfies Schwartz-type decay in the dilation parameter $r$ with constants polynomial in the archimedean spectral parameters and independent of the inducing characters and sections. It is used by [`AutomorphicForm.exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat`](thm.html#AutomorphicForm.exists_forall_exists_entire_whittakerCoefficient_bruhatEisenstein_eq_eulerProduct_mul_norm_tsum_le_mul_pow_archParam_weight_mul_rpow_neg_of_isCompact_of_flat), where the bound is summed over a lattice of $\xi$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat.lean

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
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ProductionPins

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_forall_exists_whittakerCoefficient_diagOne_eq_eulerProduct_mul_entire_norm_le_mul_pow_archParam_weight_dilation_of_flat
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
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (hψ : IsGlobalAddChar K ψ)
    (U : Set (AdeleRing (𝓞 K) K)ˣ) (hU : IsCompact U) (r₀ : ℝ) (hr₀ : 0 < r₀)
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), SK ⊆ S ∧
    ∀ Nd : ℕ, ∃ (C : ℝ) (A : ℕ), 0 < C ∧
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
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ)),
    let E : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s h =>
      ψf s h + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K *
        unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * h)
    ∃ 𝒥 : {ξ : K // ξ ≠ 0} → ℂ → (AdeleRing (𝓞 K) K)ˣ → ℂ,
      (∀ (ξ : {ξ : K // ξ ≠ 0}) (y : (AdeleRing (𝓞 K) K)ˣ),
        AnalyticOnNhd ℂ (fun s => 𝒥 ξ s y) Set.univ) ∧
      (∀ (ξ : {ξ : K // ξ ≠ 0}) (s : ℂ) (y : (AdeleRing (𝓞 K) K)ˣ), 1 < s.re →
        whittakerCoefficient K (productionPins K) ψ (E s) (ξ : K) (diagOne y)
          = (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
              (1 - ((NumberField.TateGlobal.localChar (μ * ν⁻¹) v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1)))) * 𝒥 ξ s y) ∧
      (∀ ξ : {ξ : K // ξ ≠ 0}, Continuous (fun p : ℂ × (AdeleRing (𝓞 K) K)ˣ => 𝒥 ξ p.1 p.2)) ∧
      (∀ (ξ : {ξ : K // ξ ≠ 0}) (η : Kˣ) (s : ℂ) (y : (AdeleRing (𝓞 K) K)ˣ),
        𝒥 ξ s (Units.map (algebraMap K (AdeleRing (𝓞 K) K)) η * y)
          = 𝒥 ⟨(ξ : K) * η, mul_ne_zero ξ.2 η.ne_zero⟩ s y) ∧
      (∀ (C₁ : Set ℂ) (U₁ : Set (AdeleRing (𝓞 K) K)ˣ) (r₁ : ℝ), IsCompact C₁ → IsCompact U₁ → 0 < r₁ →
        ∃ (k₁ : ℕ) (I₁ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K), ∀ N₁ : ℕ, ∃ c₁ : ℝ,
          ∀ s ∈ C₁, ∀ u ∈ U₁, ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (r : ℝ), r₁ ≤ r →
            (z : AdeleRing (𝓞 K) K).2 = 1 →
            (∀ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w ((z : AdeleRing (𝓞 K) K).1 w) = (r : ℂ)) →
            ∀ ξ : {ξ : K // ξ ≠ 0},
              ((ξ : K) ∉ I₁ → 𝒥 ξ s (z * u) = 0) ∧
              ‖𝒥 ξ s (z * u)‖ ≤ c₁ * r ^ ((Module.finrank ℚ K : ℝ) * (1 / 2 - s.re)) *
                (max 1 ((|Algebra.norm ℚ (ξ : K)| : ℚ) : ℝ)) ^ k₁ *
                (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + r * |(mixedEmbedding K (ξ : K)).1 w|) ^ (-(N₁ : ℝ))) *
                ∏ w : {w : InfinitePlace K // w.IsComplex},
                  (1 + r * ‖(mixedEmbedding K (ξ : K)).2 w‖) ^ (-(2 * N₁ : ℝ))) ∧
      (∀ (t : ℝ), ∀ u ∈ U, ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (r : ℝ), r₀ ≤ r →
        (z : AdeleRing (𝓞 K) K).2 = 1 →
        (∀ w : InfinitePlace K, InfinitePlace.Completion.extensionEmbedding w ((z : AdeleRing (𝓞 K) K).1 w) = (r : ℂ)) →
        ∀ ξ : {ξ : K // ξ ≠ 0},
          ((ξ : K) ∉ I → 𝒥 ξ ((t : ℂ) * Complex.I) (z * u) = 0) ∧
          ‖𝒥 ξ ((t : ℂ) * Complex.I) (z * u)‖ ≤
            C * (1 + ∑ v : InfinitePlace K, (|t + τμ v| + |t - τν v| + (|mμ v| : ℝ) + (|mν v| : ℝ))) ^ A *
              r ^ ((Module.finrank ℚ K : ℝ) * (1 / 2)) *
              (max 1 ((|Algebra.norm ℚ (ξ : K)| : ℚ) : ℝ)) ^ k *
              (∏ w : {w : InfinitePlace K // w.IsReal}, (1 + r * |(mixedEmbedding K (ξ : K)).1 w|) ^ (-(Nd : ℝ))) *
              ∏ w : {w : InfinitePlace K // w.IsComplex},
                (1 + r * ‖(mixedEmbedding K (ξ : K)).2 w‖) ^ (-(2 * Nd : ℝ))) := by sorry
