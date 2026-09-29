-- Prove2me | Theorems.Thm_EisensteinGeneral_Piece_exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule
-- name    : EisensteinGeneral.Piece.exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:40.316651+00:00
-- url     : https://prove2.me/theorems/fbb39cf4-54d8-52a6-8ab1-24490b78375b
-- title:
--   Uniform factorisation datum at the identity for flat Eisenstein pieces
-- statement:
--   Fixed global data. Let $K$ be a number field, $S_K$ a finite set of finite places of $K$, and $\xi_K$ a homomorphism from the full unit group $(\mathbb{A}_K)^\times$ (realised as the top subgroup) to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function (`hξc`) and trivial on the image of $K^\times$ (`hξt`). Let $N$ be an ideal of $\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`), let `tysK` be an `ArchTypeFamily` for $K$, i.e. a number $\mathrm{card}(w)$ of archimedean types at each infinite place $w$ together with, for each index, a representation of the row-isometry subgroup of $\mathrm{GL}_2(K_w)$ on some $\mathbb{C}^n$, and let $w \in \mathbb{R}$ be such that $\|\xi_K(z)\| = \mathrm{ideleNorm}_K(z)^{w}$ for all $z$, where $\mathrm{ideleNorm}_K$ is the distributive Haar character of $\mathbb{A}_K$ (`hξw`). Let $\psi$ be an additive character of $\mathbb{A}_K$ which is global in the sense of `IsGlobalAddChar` (trivial on $K$, continuous, nontrivial), let $\psi_v$ be additive characters of the completions $K_v$ at the finite places, and let $n_\psi : v \mapsto n_\psi(v) \in \mathbb{Z}$ have finite support. The hypotheses on this character data are: $\psi_v$ is trivial on $\{x : v(x) \le \exp(n_\psi(v))\}$; $\psi_v$ is nontrivial on $\{x : v(x) \le \exp(n_\psi(v)+1)\}$ (so $n_\psi(v)$ is the exact level); and $\psi$ restricted to the finite adeles is the (finitely supported) product $\prod_v \psi_v(x_v)$. Finally, let $\theta_r$ be nonzero reals indexed by the real places and $\theta_c$ nonzero complex numbers indexed by the complex places, such that on the infinite part $\psi$ is given, for $p$ in the mixed space of $K$, by $\psi = \prod_{i \text{ real}} \exp(-2\pi i\,\theta_r(i)\,p_1(i)) \cdot \prod_{w \text{ complex}} \exp(-4\pi i\,\mathrm{Re}(\theta_c(w)\,p_2(w)))$.
--
--   Throughout, $\alpha_m$ denotes the monoid homomorphism $(\mathbb{A}_K)^\times \to \mathbb{R}^\times$ obtained from the distributive Haar character of $\mathbb{A}_K$ via $\mathbb{R}_{\ge 0} \to \mathbb{R}$, and the adele ring carries its Borel measurable structure.
--
--   Uniform constants. The assertion is that there exist a finite set $S_0$ of finite places, natural numbers $n_0, k_0, m_0, c_0, L$, menus $A^{\mathrm{menu}}, B^{\mathrm{menu}} : \mathrm{Fin}\,L \to (v) \to K_v \to \mathbb{C}$ and a real $C_0$, such that $S_K \subseteq S_0$; $n_\psi(v) = 0$ for every $v \notin S_0$; $0 \le C_0$, $1 \le m_0$ and $1 \le c_0$; for every $l$ and $v$ the function $A^{\mathrm{menu}}_l(v)$ is constant on congruence classes modulo $\mathfrak{p}_v^{m_0}$ within the valuation ring, i.e. $A^{\mathrm{menu}}_l(v)(y) = A^{\mathrm{menu}}_l(v)(x)$ whenever $x,y \in \mathcal{O}_v$ and $v(y-x) \le \mathrm{ofAdd}(-m_0)$; and $B^{\mathrm{menu}}_l(v)$ is constant on such congruence classes in all of $K_v$.
--
--   Data quantified after the constants. These constants serve for all of the following: a proof $h_{\alpha_m}$ that $\alpha_m$ takes positive values; characters $\mu, \nu : (\mathbb{A}_K)^\times \to \mathbb{C}^\times$ which are unitary ($\|\mu(x)\| = 1$, likewise $\nu$), are idele class characters (trivial on the image of $K^\times$), are continuous as $\mathbb{C}$-valued functions, and satisfy $\mu(z)\nu(z)\,\mathrm{ideleNorm}_K(z)^{w} = \xi_K(z)$ for all $z$; families $\tau_\mu, \tau_\nu : \mathrm{InfinitePlace}(K) \to \mathbb{R}$ such that at every infinite place $v$ and every unit $x$ of $K_v$ whose extension embedding has positive real part and vanishing imaginary part, the archimedean local component of $\mu$ at $v$ equals $\mathrm{ideleNorm}_K(\mathrm{archUnitHom}_v(x))^{\tau_\mu(v) i}$, and likewise for $\nu$ with $\tau_\nu$; integer families $m_\mu, m_\nu : \mathrm{InfinitePlace}(K) \to \mathbb{Z}$ such that on elements of norm one the archimedean local component of $\mu$ at $v$ equals the $m_\mu(v)$-th power of the extension embedding, and likewise for $\nu$; and a family $\psi_f : \mathbb{C} \to \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ subject to the following group of hypotheses: for each $s$, $\psi_f(s)$ is an induced section for the pair $(\mu \cdot \alpha_m^{\,s+1/2},\ \nu \cdot \alpha_m^{-(s+1/2)})$, i.e. $\psi_f(s)(bg)$ equals the product of the two characters evaluated on the diagonal entries of $b$ times $\psi_f(s)(g)$ for $b$ in the adelic Borel subgroup; each $\psi_f(s)$ is archimedean $K$-finite at every infinite place and $K_f$-smooth (its stabiliser in the finite adelic subgroup, the kernel of the archimedean projection, is open); $(s,g) \mapsto \psi_f(s)(g)$ is jointly continuous; $s \mapsto \psi_f(s)(g)$ is entire for each $g$; at each infinite place there is a finite-dimensional $\mathbb{C}$-submodule $W$ of functions on the archimedean row-isometry subgroup containing every right-translate function $k \mapsto \psi_f(s)(gk)$, uniformly in $s$ and $g$; the family is flat, $\psi_f(s)(k) = \psi_f(0)(k)$ for $k$ in the adelic maximal compact subgroup; it is right invariant under $\mathrm{principalLevel}(N) \cap$ the finite adelic subgroup; each $\psi_f(s)$ lies in the archimedean cut submodule $\mathrm{archCutSubmodule}(K, \mathrm{tysK})$; the normalisation $\int_{\mathbf{K}} \|\psi_f(0)(k)\|^2 \, d(\mathrm{maximalCompactHaar}) \le 1$ holds; and $\psi_f$ is not identically zero. Finally, uniformisers $\varpi_v$ with $v(\varpi_v) = \mathrm{ofAdd}(-1)$ at every finite place, and a finite set $S \supseteq S_0$ of finite places.
--
--   Conclusion. For all such data there exists a factorisation datum $D$ of type $\mathrm{FactorizationDatum}(K, \psi_v, n_\psi, \mu\nu^{-1}, \varpi, \psi_f, 1, S)$ — the structure recording a rank $n$, depths $c_S$ and $m_S$, local integrands $A, B$ and $h$ at the finite places, archimedean exponents $\mathrm{kdat}, \tau_r$ at the real places and $\mathrm{abm}, \tau_c$ at the complex places, archimedean profiles $W_r, W_c$, an idele $a$, an adele $u$ and scalars $C_j(s)$, together with its built-in conditions: the local component of $\chi = \mu\nu^{-1}$ at $v$ has modulus one on $\varpi_v$; $\chi$ is trivial on the norm-one units at each $v \notin S$; $n_\psi$ vanishes off $S$; $c_S(v) \ge 1$ on $S$ and $\chi_v$ is trivial on the higher units of level $c_S(v)$ there; $m_S \ge 1$; $A_j(v)$ and $B_j(v)$ are constant on congruence classes modulo $\mathfrak{p}_v^{m_S}$ (on $\mathcal{O}_v$, respectively on $K_v$) for $v \in S$; for $v \notin S$ the integrand $h_j(v)(s)$ is the indicator of $\mathcal{O}_v$ plus, on the complement, $\chi_v^{-1}(y)\,|y|_v^{-(2s+1)}$; and the further conditions of the structure expressing that these data factorise the family $\psi_f$ at $g = 1$ over $S$ — such that: $D.n \le n_0$; $D.a = 1$; $D.u = 0$; $D.m_S = m_0$; $D.c_S(v) = c_0$ for every $v \in S$; $D.\tau_r(j)(i) = \tau_\mu(i) - \tau_\nu(i)$ at every real place $i$ and every $j$; $D.\tau_c(j)(w) = 2(\tau_\mu(w) - \tau_\nu(w))$ at every complex place $w$ and every $j$; $|D.\mathrm{kdat}(j)(i)| \le k_0$ at the real places; the third component of $D.\mathrm{abm}(j)(w)$ is at most $k_0$ at the complex places; for every $j$ and $v$ there is an index $l$ with $D.A(j)(v) = A^{\mathrm{menu}}_l(v)$, and likewise an index with $D.B(j)(v) = B^{\mathrm{menu}}_l(v)$; the scalars are constant in $s$, $D.C(j)(s) = D.C(j)(0)$; and $\|D.C(j)(0)\|^2 \le C_0 \int_{\mathbf{K}} \|\psi_f(0)(k)\|^2 \, d(\mathrm{maximalCompactHaar})$ for every $j$.
--
--   This is the uniform form, at the identity element $g = 1$, of the factorisation of a flat Eisenstein piece into finitely many products of local integrands: the size of the datum, the depths $m_0, c_0$, the archimedean exponent bound $k_0$, the finite menu of ramified local integrands and the constant $C_0$ are all chosen before the characters $\mu, \nu$, the section family and the uniformisers, while only the scalars $C_j$ — controlled by the $L^2$-norm of $\psi_f(0)$ over the maximal compact subgroup — and the explicit archimedean exponents depend on those. It feeds the Whittaker-coefficient computation for Bruhat–Eisenstein integrals at the diagonal identity, where the uniformity in $(\mu,\nu)$ and in the section is what permits Euler-product and norm bounds on balls in the strip.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_EisensteinGeneral_Piece_exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule.lean

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
import Definitions.Def_EisensteinGeneral_FactorizationDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open AutomorphicForm
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem EisensteinGeneral.Piece.exists_forall_exists_factorizationDatum_one_uniform_of_flat_principalLevel_archCutSubmodule
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
    (ψ : AddChar (AdeleRing (𝓞 K) K) ℂ) (_hψ : IsGlobalAddChar K ψ)
    (ψv : (v : HeightOneSpectrum (𝓞 K)) → AddChar (v.adicCompletion K) ℂ)
    (nψ : HeightOneSpectrum (𝓞 K) → ℤ)
    (_hnψfin : (Function.support nψ).Finite)
    (_hψv : ∀ (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K),
      Valued.v x ≤ WithZero.exp (nψ v) → ψv v x = 1)
    (_hψv' : ∀ v : HeightOneSpectrum (𝓞 K),
      ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (nψ v + 1) ∧ ψv v x ≠ 1)
    (_hψfin : ∀ x : FiniteAdeleRing (𝓞 K) K,
      ψ (AddMonoidHom.inr (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) x)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), ψv v (x v))
    (θr : {w : InfinitePlace K // w.IsReal} → ℝ) (_hθr : ∀ i, θr i ≠ 0)
    (θc : {w : InfinitePlace K // w.IsComplex} → ℂ) (_hθc : ∀ w, θc w ≠ 0)
    (_hψarch : ∀ p : mixedEmbedding.mixedSpace K,
      ψ (AddMonoidHom.inl (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm p))
      = (∏ i : {w : InfinitePlace K // w.IsReal},
      Complex.exp (-(((2 * Real.pi * θr i * p.1 i : ℝ) : ℂ) * Complex.I)))
      * ∏ w : {w : InfinitePlace K // w.IsComplex},
      Complex.exp (-(((4 * Real.pi * (θc w * p.2 w).re : ℝ) : ℂ) * Complex.I)))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (n₀ k₀ m₀ c₀ L : ℕ)
      (Amenu Bmenu : Fin L → (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K → ℂ) (C₀ : ℝ),
      SK ⊆ S₀ ∧ (∀ v ∉ S₀, nψ v = 0) ∧ 0 ≤ C₀ ∧ 1 ≤ m₀ ∧ 1 ≤ c₀ ∧
      (∀ (l : Fin L) (v : HeightOneSpectrum (𝓞 K)), ∀ x ∈ v.adicCompletionIntegers K,
        ∀ y ∈ v.adicCompletionIntegers K,
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m₀ : ℤ)) → Amenu l v y = Amenu l v x) ∧
      (∀ (l : Fin L) (v : HeightOneSpectrum (𝓞 K)) (x y : v.adicCompletion K),
          Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m₀ : ℤ)) → Bmenu l v y = Bmenu l v x) ∧
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
      (_hψfne : ∃ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ψf s g ≠ 0)
      (ϖ : (v : HeightOneSpectrum (𝓞 K)) → (v.adicCompletion K)ˣ)
      (_hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion K) = Multiplicative.ofAdd (-1 : ℤ))
      (S : Finset (HeightOneSpectrum (𝓞 K))) (_hS : S₀ ⊆ S),
    ∃ D : EisensteinGeneral.Piece.FactorizationDatum K ψv nψ (μ * ν⁻¹) ϖ ψf (1 : AdelicGL2 (𝓞 K) K) S,
      D.n ≤ n₀ ∧ D.a = 1 ∧ D.u = 0 ∧ D.mS = m₀ ∧
      (∀ v ∈ S, D.cS v = c₀) ∧
      (∀ (j : Fin D.n) (i : {w : InfinitePlace K // w.IsReal}), D.τr j i = τμ i.1 - τν i.1) ∧
      (∀ (j : Fin D.n) (w : {w : InfinitePlace K // w.IsComplex}), D.τc j w = 2 * (τμ w.1 - τν w.1)) ∧
      (∀ (j : Fin D.n) (i : {w : InfinitePlace K // w.IsReal}), |D.kdat j i| ≤ (k₀ : ℤ)) ∧
      (∀ (j : Fin D.n) (w : {w : InfinitePlace K // w.IsComplex}), (D.abm j w).2.2 ≤ k₀) ∧
      (∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 K)), ∃ l : Fin L, D.A j v = Amenu l v) ∧
      (∀ (j : Fin D.n) (v : HeightOneSpectrum (𝓞 K)), ∃ l : Fin L, D.B j v = Bmenu l v) ∧
      (∀ (j : Fin D.n) (s : ℂ), D.C j s = D.C j 0) ∧
      (∀ j : Fin D.n, ‖D.C j 0‖ ^ 2
          ≤ C₀ * ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) := by sorry
