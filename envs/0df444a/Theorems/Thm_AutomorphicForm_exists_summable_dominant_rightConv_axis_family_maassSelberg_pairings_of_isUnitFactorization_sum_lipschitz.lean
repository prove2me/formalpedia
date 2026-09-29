-- Prove2me | Theorems.Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz
-- name    : AutomorphicForm.exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/74af745b-83e6-5e20-bff2-268a0c4e3d3a
-- title:
--   Summable dominant for continuous-spectrum Maass–Selberg pairings
-- statement:
--   Throughout, $K$ is a number field, and the group in play is $\mathrm{GL}_2$ of the adele ring of $K$, written `AdelicGL2 (𝓞 K) K`.
--
--   **Outer data and hypotheses.** Two reals $\alpha<\beta$ with $0<\alpha$ are fixed, together with a set $\Phi_K$ of adelic matrices. A *Siegel covering group* of hypotheses is imposed: reals $c_K,u_K,d_{1K},d_{2K}$ with $0<c_K$, $0<d_{1K}<d_{2K}$ and a finite set $T_K$ of adelic matrices are given, and `hcovK` says that the union over $x\in T_K$ of the right translates by $x$ of the cut Siegel set $\mathrm{centreCutSiegelSet}\,K\,c_K\,u_K\,d_{1K}\,d_{2K}$ — the set of $g$ whose finite part lies in `finiteIntegralGL2`, whose archimedean component at each infinite place has local height at least $c_K$ and window quantity $\mathrm{xWindowSq}\le u_K^2$, and whose archimedean determinant norm at each infinite place lies in $[d_{1K},d_{2K}]$ — covers $\mathrm{GL}_2$ of the adeles modulo the centre, in the sense that every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and an idele $z$ with $\gamma g\,z\in$ that union. A *central group*: the idele group carries a measurable structure which is the Borel structure of its topology, $\nu_{ZK}$ is a Haar measure on it, and $\Omega_K$ is a fundamental domain for the action of the group of principal ideles (the range of $K^\times\to\mathbb{A}_K^\times$) with respect to $\nu_{ZK}$.
--
--   A *central-character group*: $S_K$ is a finite set of finite places, $\xi_K$ is a character of the full idele group (formally, of the subgroup $\top$) with values in $\mathbb{C}^\times$, continuous as a function into $\mathbb{C}$ (`hξc`), trivial on principal ideles (`hξt`), and of modulus $\|z\|^{w}$ for a fixed real $w$, where $\|\cdot\|$ is the idele norm [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19) given by the Haar modulus character (`hξw`). A *level and type group*: an ideal $N\subseteq\mathcal{O}_K$ all of whose prime divisors lie in $S_K$ (`hN`), and an archimedean type family $\mathrm{tys}_K$, i.e. for each infinite place finitely many representations of the row-isometry group of the completion. Finally local test factors: a function $f_{aK}$ on $\mathrm{GL}_2$ of the infinite adeles and, for each finite place $v$, a function $f_{SK}(v)$ on $\mathrm{GL}_2(K_v)$.
--
--   **The modulus character.** The conclusion first introduces $\alpha_m$, the unit-valued homomorphism from the idele group to $\mathbb{R}^\times$ obtained from the distributive Haar character of the adele ring by passing from $\mathbb{R}_{\ge0}$ to $\mathbb{R}$, and equips the adele ring with its Borel structure; $h_{\alpha m}$ asserts $\alpha_m(x)>0$ for all $x$.
--
--   **Eisenstein data (further universally quantified).** A countable type $\iota_E$, and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}_K^\times,\mathbb{C}^\times)$ subject to: each $\mu_e,\nu_e$ is unitary ($|\mu_e(z)|=|\nu_e(z)|=1$ for all $z$), each is trivial on principal ideles, each is continuous as a $\mathbb{C}$-valued function, the relation $\mu_e(z)\nu_e(z)\|z\|^{w}=\xi_K(z)$ holds for all $e,z$, and distinct indices are separated: for $e\ne e'$ there is a norm-one idele (an element of the kernel of the Haar modulus character) at which $\mu_e\ne\mu_{e'}$ or $\nu_e\ne\nu_{e'}$.
--
--   Next, for each $e$ an integer $n_E(e)$ and a family $\varphi_{E}(e,j):\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$, $j\in\mathrm{Fin}(n_E(e))$, with the following groups of hypotheses. *Induced-section and regularity*: for all $e,j,s$, $\varphi_E(e,j,s)$ is a section of the induced model for the pair $\big(\mu_e\,\alpha_m^{s+1/2},\ \nu_e\,\alpha_m^{-(s+1/2)}\big)$, meaning $\varphi(bg)$ equals the product of the first character at the $(0,0)$ entry of $b$, the second character at the $(1,1)$ entry of $b$, and $\varphi(g)$ for $b$ in the adelic Borel subgroup; it is archimedean $K$-finite at every infinite place; it is smooth for the finite adelic subgroup (kernel of the archimedean projection), i.e. its stabiliser there is open; $(s,g)\mapsto\varphi_E(e,j,s,g)$ is continuous; $s\mapsto\varphi_E(e,j,s,g)$ is entire; and at each infinite place the right translates under the archimedean row-isometry subgroup lie in one finite-dimensional subspace $W$, uniformly in $s$ and $g$. *Flatness, level and type*: $\varphi_E(e,j,s,k)=\varphi_E(e,j,0,k)$ for $k$ in the adelic maximal compact subgroup (finite part integral, archimedean components row isometries); $\varphi_E(e,j,s)$ is right invariant under the intersection of the principal level subgroup of $N$ with the finite adelic subgroup; and $\varphi_E(e,j,s)$ lies in the archimedean cut submodule of the type family $\mathrm{tys}_K$, the infimum over infinite places of the span of the type submodules attached to the representations of the family. *Orthonormality*: $\int \varphi_E(e,i,0,k)\overline{\varphi_E(e,j,0,k)}\,d(\mathrm{maximalCompactHaar}\,K)$ equals $1$ if $i=j$ and $0$ otherwise. *Completeness on the axis* (`_hφEspan`): for each $e$, each real $t$ and each $\varphi_0$ which is an induced section for the pair at $s=it$, continuous, archimedean $K$-finite, invariant under the level subgroup and in the cut submodule, $\varphi_0$ lies in the complex span of the $\varphi_E(e,j,it)$, $j\in\mathrm{Fin}(n_E(e))$. *Exhaustion of pairs* (`_hpairs`): for every pair of characters $\mu',\nu'$ which are unitary, trivial on principal ideles, continuous and satisfy $\mu'\nu'\|\cdot\|^{w}=\xi_K$, and every real $t$ and nonzero $\varphi_0$ with the same list of properties at $s=it$, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on norm-one ideles.
--
--   Further, for each $e,j$ a set $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E(e,j),N_E(e,j)$ of $(s,g)$, subject to `_hEE` (a nine-fold conjunction): $O_E(e,j)$ is open, preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for every $g$ the functions $s\mapsto E_E(e,j,s,g)$ and $s\mapsto N_E(e,j,s,g)$ are analytic on a neighbourhood of $O_E(e,j)$; both are continuous in $(s,g)$ on $O_E(e,j)\times\mathrm{univ}$; for $\mathrm{Re}\,s>1/2$, $E_E(e,j,s,g)=\varphi_E(e,j,s,g)+\sum_{\xi\in K}\varphi_E\big(e,j,s,\,\mathrm{adelicWeyl}\cdot u(\xi)\cdot g\big)$ with $u(\xi)$ the upper unipotent matrix with entry the image of $\xi$; and for $\mathrm{Re}\,s>1/2$, $N_E(e,j,s,g)$ equals the Weyl intertwining integral $\int \varphi_E(e,j,s)\big(\mathrm{adelicWeyl}^{-1}u(x)g\big)\,dx$ against the adelic additive Haar measure. A dichotomy `_hdiag`: for each $e$, either $\mu_e=\nu_e$ or the two differ at some norm-one idele.
--
--   **Test function.** Finally, $f_0$ is a continuous compactly supported function on $\mathrm{GL}_2(\mathbb{A}_K)$, $f_{f0}$ a function on $\mathrm{GL}_2$ of the finite adeles, and the hypothesis `IsUnitFactorization K SK f₀ faK ff₀ fSK` holds: $f_{aK}$ is an archimedean test factor (of the form $\Phi$ applied to the mixed-space entries with $\Phi$ smooth, and compactly supported), $f_{f0}$ is locally constant with compact support, $f_{SK}(v)$ is locally constant with compact support for $v\in S_K$, $f_{f0}(h)$ equals $\prod_{v\in S_K}f_{SK}(v)(h_v)$ whenever $h_v$ is integral at every $v\notin S_K$ and vanishes when some such component is not integral, and $f_0(g)=f_{aK}(g_\infty)\,f_{f0}(g_{\mathrm{fin}})$.
--
--   **The pairings.** With $\langle\cdot,\cdot\rangle$ denoting the integral over the adelic maximal compact subgroup against `maximalCompactHaar K`, and with $V_{\mathrm{box}}$ the real volume of the adelic box for the adelic additive Haar measure, the statement defines for $e\in\iota_E$, $i,j\in\mathrm{Fin}(n_E(e))$ and $t\in\mathbb{R}$:
--   $$a_{e,ij}(t)=\Big\langle \big(\varphi_E(e,j,it)\cdot\|\det\|^{w/2}\big)\star f_0,\ \varphi_E(e,i,it)\Big\rangle,$$
--   where the right convolution is $(\phi\star f_0)(g)=\int\phi(gx)f_0(x)\,dx$ against the adelic $\mathrm{GL}_2$ Haar measure and $\|\det\|$ is the idele norm of the determinant;
--   $$P_{e,ij}(t)=\big\langle \varphi_E(e,i,it),\varphi_E(e,j,it)\big\rangle,\qquad Q_{e,ij}(t)=\big\langle V_{\mathrm{box}}^{-1}N_E(e,i,it),\ V_{\mathrm{box}}^{-1}\partial_s N_E(e,j,\cdot)\big|_{s=it}\big\rangle;$$
--   $U_{e,ij}(t)=\big\langle\varphi_E(e,i,it),\ V_{\mathrm{box}}^{-1}N_E(e,j,it)\big\rangle$ and $V_{e,ij}(t)=\big\langle V_{\mathrm{box}}^{-1}N_E(e,i,it),\ \varphi_E(e,j,it)\big\rangle$ when $\mu_e=\nu_e$, and $U_{e,ij}=V_{e,ij}=0$ otherwise.
--
--   **Conclusion.** The assertion is the conjunction of: (i) continuity in $t$ of every $a_{e,ij}$; (ii) continuity of every $Q_{e,ij}$; (iii) continuity of every $U_{e,ij}$; (iv) continuity of every $V_{e,ij}$; (v) integrability on $\mathbb{R}$ of every $a_{e,ij}$; (vi) integrability of $t\mapsto a_{e,ij}(t)Q_{e,ij}(t)$; (vii) integrability of $t\mapsto a_{e,ij}(t)U_{e,ij}(t)$; (viii) integrability of $t\mapsto a_{e,ij}(t)V_{e,ij}(t)$; and (ix) the existence of a summable function $L:\iota_E\to\mathbb{R}$ such that for every $e$:
--   $$\sum_{i}\sum_{j}\int_{\mathbb{R}}\Big(\|a_{e,ij}(t)\|\big(1+\|P_{e,ij}(t)\|\big)+\|a_{e,ij}(t)Q_{e,ij}(t)\|+\|a_{e,ij}(t)U_{e,ij}(t)\|+\|a_{e,ij}(t)V_{e,ij}(t)\|\Big)\,dt\le L(e),$$
--   $$\sum_i\sum_j\|a_{e,ij}(0)\|\big(\|U_{e,ij}(0)\|+\|V_{e,ij}(0)\|\big)\le L(e),$$
--   and, for every real $t$ with $|t|\le 1$, both
--   $$\sum_i\sum_j\big\|a_{e,ij}(t)\big(U_{e,ij}(t)+V_{e,ij}(t)\big)-a_{e,ij}(0)\big(U_{e,ij}(0)+V_{e,ij}(0)\big)\big\|\le L(e)\,|t|$$
--   and
--   $$\sum_i\sum_j\big\|a_{e,ij}(t)\big(U_{e,ij}(t)-V_{e,ij}(t)\big)\big\|\le L(e)\,|t|.$$
--   The sums over $i$ and $j$ are the finite sums over $\mathrm{Fin}(n_E(e))$, and the integral in the first display is with respect to Lebesgue measure on $\mathbb{R}$.
--
--   This is the analytic input for the continuous (Eisenstein) block of the trace formula for $\mathrm{GL}_2$ over a number field: it produces a single summable majorant $L$ controlling, simultaneously in the Eisenstein datum $e$ and in the spectral parameter $t$, the matrix coefficients of the induced representation at $s=it$ against the test function, the Maass–Selberg pairings involving the intertwining operator and its $s$-derivative, together with Lipschitz control at $t=0$ of the symmetric and antisymmetric combinations of $U$ and $V$. Such a dominant is what allows the contribution of the continuous spectrum to be summed over $e$ and integrated over $t$ term by term; it is used by [`AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul`](thm.html#AutomorphicForm.exists_atomic_forall_tendsto_setIntegral_lambdaT_finsum_sub_lambdaT_tsum_sub_lambdaT_finsum_chiDet_sub_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.exists_summable_dominant_rightConv_axis_family_maassSelberg_pairings_of_isUnitFactorization_sum_lipschitz
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
      (f₀ : AdelicGL2 (𝓞 K) K → ℂ) (_hf₀ : Continuous f₀) (_hf₀c : HasCompactSupport f₀)
      (ff₀ : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ),
      IsUnitFactorization K SK f₀ faK ff₀ fSK →
    let a : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, rightConv K (fun g : AdelicGL2 (𝓞 K) K => φE e j ((t : ℂ) * Complex.I) g *
          (((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g)) ^ (w / 2) : ℝ) : ℂ)) f₀ (k : AdelicGL2 (𝓞 K) K) *
        conj (φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    let P : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    let Q : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      ∫ k, (fun g => (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K) *
        conj ((fun g => (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * deriv (fun s : ℂ => NE e j s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
    let U : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      if μ e = ν e then
        ∫ k, φE e i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((fun g => (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE e j ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
      else 0
    let V : ∀ e : ιE, Fin (nE e) → Fin (nE e) → ℝ → ℂ := fun e i j t =>
      if μ e = ν e then
        ∫ k, (fun g => (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE e i ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 K) K) *
          conj (φE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)
      else 0
    (∀ e i j, Continuous (a e i j)) ∧ (∀ e i j, Continuous (Q e i j)) ∧
    (∀ e i j, Continuous (U e i j)) ∧ (∀ e i j, Continuous (V e i j)) ∧
    (∀ e i j, Integrable (a e i j)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * Q e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * U e i j t)) ∧
    (∀ e i j, Integrable (fun t => a e i j t * V e i j t)) ∧
    ∃ L : ιE → ℝ, Summable L ∧
      (∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e),
        ∫ t : ℝ, (‖a e i j t‖ * (1 + ‖P e i j t‖) + ‖a e i j t * Q e i j t‖ +
          ‖a e i j t * U e i j t‖ + ‖a e i j t * V e i j t‖) ≤ L e) ∧
      (∀ e, ∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j 0‖ * (‖U e i j 0‖ + ‖V e i j 0‖) ≤ L e) ∧
      (∀ (e : ιE) (t : ℝ), |t| ≤ 1 →
        (∑ i : Fin (nE e), ∑ j : Fin (nE e),
          ‖a e i j t * (U e i j t + V e i j t) - a e i j 0 * (U e i j 0 + V e i j 0)‖) ≤ L e * |t| ∧
        (∑ i : Fin (nE e), ∑ j : Fin (nE e), ‖a e i j t * (U e i j t - V e i j t)‖) ≤ L e * |t|) := by sorry
