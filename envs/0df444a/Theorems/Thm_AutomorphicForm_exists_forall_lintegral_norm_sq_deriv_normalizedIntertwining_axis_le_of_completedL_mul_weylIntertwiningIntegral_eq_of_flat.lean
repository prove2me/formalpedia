-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
-- name    : AutomorphicForm.exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/1123d0e1-3b2b-529f-8fe9-8fa21780a791
-- title:
--   Uniform L² bound for the axis derivative of R(s)
-- statement:
--   Fix a number field $K$, with the unit group $(\mathbf A_K)^\times$ of its adele ring carrying a Borel measurable structure. The data fixed in advance are: a finite set $S_K$ of finite places of $K$; a homomorphism $\xi_K$ from the full subgroup $\top$ of $(\mathbf A_K)^\times$ to $\mathbb C^\times$, whose associated function $z\mapsto \xi_K(z)$ is continuous (`hξc`) and which is trivial on the image of $K^\times$ under the diagonal embedding (`hξt`); an ideal $N$ of $\mathcal O_K$ such that every finite place $v$ with $v \mid N$ belongs to $S_K$ (`hN`); an archimedean type family `tysK`, that is, for each infinite place $w$ a natural number $\mathrm{card}(w)$ together with $\mathrm{card}(w)$ data `ArchRepAt`, each consisting of a dimension $n$ and a representation of the row-isometry subgroup $\mathrm{rowIsometrySubgroup}_0$ of $GL_2(K_w)$ on $\mathbb C^n$; and a real number $w$ such that $\|\xi_K(z)\| = \|z\|^{w}$ for all ideles $z$, where $\|z\|$ is the idele norm $\mathrm{ideleNorm}$, i.e. the value of the distributive Haar character of $\mathbf A_K$ at $z$ (`hξw`).
--
--   Write $\alpha_m \colon (\mathbf A_K)^\times \to \mathbb R^\times$ for the module character obtained from the distributive Haar character of $\mathbf A_K$ through $\mathbb R_{\ge 0} \to \mathbb R$, and give $\mathbf A_K$ its Borel structure.
--
--   The assertion is that there exist a real $C > 0$ and a natural number $A$, depending only on the data above, such that the following holds for every choice of the data listed next.
--
--   First, a proof `hαm` that $\alpha_m(x) > 0$ for all $x$ (needed to form the complex powers below), and two homomorphisms $\mu, \nu \colon (\mathbf A_K)^\times \to \mathbb C^\times$ subject to: unitarity, $\|\mu(x)\| = \|\nu(x)\| = 1$ for all $x$ (`_hμ`, `_hν`); triviality on principal ideles, $\mu(u) = \nu(u) = 1$ for $u \in K^\times$ (`_hμic`, `_hνic`); continuity of the associated complex-valued functions (`_hμc`, `_hνc`); and the central-character relation $\mu(z)\,\nu(z)\,\|z\|^{w} = \xi_K(z)$ for all ideles $z$ (`_hμν`). Next, families of real numbers $\tau_\mu, \tau_\nu$ indexed by the infinite places, such that for every infinite place $v$ and every unit $x$ of $K_v$ whose image under the extension embedding is a positive real number, the local archimedean component $\mathrm{archLocalChar}\,\mu\,v$ (the composite of $\mu$ with the map sending $x$ to the idele equal to $x$ at $v$ and $1$ elsewhere) takes the value $\|\mathrm{archUnitHom}_v(x)\|^{\,\tau_\mu(v) i}$, and likewise for $\nu$ with $\tau_\nu$ (`_hτμ`, `_hτν`); and families of integers $m_\mu, m_\nu$ indexed by the infinite places such that for every $v$ and every unit $x$ of $K_v$ of absolute value $1$, the same local archimedean characters are given by $x^{m_\mu(v)}$, respectively $x^{m_\nu(v)}$ (`_hmμ`, `_hmν`).
--
--   Next, a family $\psi f \colon \mathbb C \to GL_2(\mathbf A_K) \to \mathbb C$ subject to eleven hypotheses. For every $s$, $\psi f(s)$ is an induced section for the pair of characters $\eta_1(s) = \mu \cdot \alpha_m^{\,s+1/2}$ and $\eta_2(s) = \nu \cdot \alpha_m^{-(s+1/2)}$: for every $b$ in the adelic Borel subgroup (matrices with vanishing lower-left entry) and every $g$, $\psi f(s)(bg) = \eta_1(s)(b_{00})\,\eta_2(s)(b_{11})\,\psi f(s)(g)$ (`_hψf`). For every $s$, $\psi f(s)$ satisfies `IsArchKFinite`, i.e. for each infinite place $w$ the predicate `RightTranslatesSpanFinite` holds for $\psi f(s)$ and the subgroup `archRowIsometrySubgroup K w`, the image in $GL_2(\mathbf A_K)$ of the row-isometry subgroup of $GL_2(K_w)$ (`_hψfK`); and $\psi f(s)$ satisfies `IsKfSmooth`, i.e. the stabiliser of $\psi f(s)$ under right translation by the subgroup of adelic matrices trivial at the infinite places (the kernel of $\mathrm{glArch}$) is open (`_hψff`). The map $(s,g) \mapsto \psi f(s)(g)$ is continuous (`_hψfjc`), and $s \mapsto \psi f(s)(g)$ is entire for each $g$ (`_hψfhol`). For each infinite place $v$ there is a finite-dimensional complex subspace $W$ of functions on `archRowIsometrySubgroup K v` containing, for all $s$ and $g$, the function $k \mapsto \psi f(s)(gk)$ (`_hψfKu`). The family is flat on the maximal compact: $\psi f(s)(k) = \psi f(0)(k)$ for all $s$ and all $k$ in `adelicMaximalCompact K`, the subgroup of those $g$ whose finite part is integral and whose archimedean component at each infinite place is a row isometry (unit determinant norm, and preservation of the sum of squared norms of the two rows) (`_hψfflat`). It is right invariant under the intersection of `principalLevel (𝓞 K) K N` (the level-$N$ subgroup intersected with its conjugate by the Weyl element) with the subgroup of matrices trivial at the infinite places (`_hψflev`). Each $\psi f(s)$ lies in `archCutSubmodule K tysK`, the intersection over the infinite places $w$ of the sum over $i$ of the type submodules `archTypeSubmoduleAt K w (tysK.rep w i)` (`_hψfty`). Finally, the normalisation $\int_{\mathbf K} \|\psi f(0)(k)\|^2 \, dk \le 1$ with respect to the Haar measure `maximalCompactHaar K` on `adelicMaximalCompact K` (`_hψfn`).
--
--   Next, a set $O_\psi \subseteq \mathbb C$ and functions $E_\psi, N_\psi \colon \mathbb C \to GL_2(\mathbf A_K) \to \mathbb C$, together with the nine-clause hypothesis `_hEψ`: $O_\psi$ is open and preconnected and contains both the imaginary axis $\{\operatorname{Re} s = 0\}$ and the half-plane $\{\operatorname{Re} s > 1/2\}$; for every $g$ the functions $s \mapsto E_\psi(s)(g)$ and $s \mapsto N_\psi(s)(g)$ are analytic on a neighbourhood of $O_\psi$; the maps $(s,g)\mapsto E_\psi(s)(g)$ and $(s,g)\mapsto N_\psi(s)(g)$ are continuous on $O_\psi \times \mathrm{univ}$; for $\operatorname{Re} s > 1/2$ and all $g$, $E_\psi(s)(g) = \psi f(s)(g) + \sum_{\xi \in K} \psi f(s)(\mathrm{adelicWeyl}\cdot u(\xi) \cdot g)$ where $u(\xi)$ is the upper unipotent matrix with entry the image of $\xi$ in $\mathbf A_K$; and for $\operatorname{Re} s > 1/2$ and all $g$, $N_\psi(s)(g)$ equals the Weyl intertwining integral $\int_{\mathbf A_K} \psi f(s)(\mathrm{adelicWeyl}^{-1} u(x) g)\,dx$ taken against the adelic additive Haar measure.
--
--   With these data set $\chi = \mu\nu^{-1}$, and define: $P(w') = \prod_{v} \bigl(1 - c_v \,(\mathrm{absNorm}\,v)^{-w'}\bigr)^{-1}$, the product over all finite places, where $c_v = \chi(\varpi_v)$ for the idele $\mathrm{uniformizerIdele}\,v$ (a uniformizer at $v$, trivial elsewhere) when $\chi$ is unramified at $v$ in the sense that its local component is trivial on the units of the ring of integers of $K_v$, and $c_v = 0$ otherwise; $\gamma(w') = \prod_{v \mid \infty} \Gamma_{\mathbb R}\bigl(w' + (\tau_\mu(v)-\tau_\nu(v))i + (|m_\mu(v)-m_\nu(v)| \bmod 2)\bigr)$ at the real places, the factor at a non-real place being $\Gamma_{\mathbb C}\bigl(w' + (\tau_\mu(v)-\tau_\nu(v))i + |m_\mu(v)-m_\nu(v)|/2\bigr)$; $c$ the reciprocal of the real volume of the adelic box (a fundamental domain for the Minkowski lattice at the infinite places times the integral finite adeles) for the adelic additive Haar measure; and $D(y) = \sum_{v \mid \infty} \bigl(|y + \tau_\mu(v)| + |y - \tau_\nu(v)| + |m_\mu(v)| + |m_\nu(v)|\bigr)$.
--
--   Finally, let $\delta > 0$ be real and let $R \colon \mathbb C \to \mathrm{adelicMaximalCompact}\,K \to \mathbb C$ be such that $s \mapsto R(s)(k)$ is analytic on a neighbourhood of $\{\operatorname{Re} s > -\delta\}$ for each $k$, the map $(s,k) \mapsto R(s)(k)$ is continuous on $\{\operatorname{Re} s > -\delta\} \times \mathrm{univ}$, and $R$ is pinned on $\operatorname{Re} s > 1/2$ by the following two requirements. If $\chi$ is not equal to $\mathrm{normPowChar}\,K\,\tau_0$, that is to $\|\cdot\|^{i\tau_0}$, for any real $\tau_0$, then for every entire $\Lambda \colon \mathbb C \to \mathbb C$ with $\Lambda(w') = \gamma(w')P(w')$ for $\operatorname{Re} w' > 1$, every $s$ with $\operatorname{Re} s > 1/2$ and every $k$ in the maximal compact,
--   $$\Lambda(2s)\,R(s)(k) = \Lambda(2s+1)\,\Bigl(c \cdot \int_{\mathbf A_K} \psi f(s)\bigl(\mathrm{adelicWeyl}^{-1} u(x) k\bigr)\,dx\Bigr).$$
--   And for every real $\tau_0$ with $\chi = \mathrm{normPowChar}\,K\,\tau_0$, for every entire $\Lambda_Q$ with $\Lambda_Q(w') = (w' + \tau_0 i)\bigl(w' - (1 - \tau_0 i)\bigr)\gamma(w')P(w')$ for $\operatorname{Re} w' > 1$, every $s$ with $\operatorname{Re} s > 1/2$ and every $k$,
--   $$(2s + \tau_0 i + 1)\,\Lambda_Q(2s)\,R(s)(k) = (2s + \tau_0 i - 1)\,\Lambda_Q(2s+1)\,\Bigl(c \cdot \int_{\mathbf A_K} \psi f(s)\bigl(\mathrm{adelicWeyl}^{-1} u(x) k\bigr)\,dx\Bigr).$$
--
--   The conclusion is the single inequality: for every real $t$,
--   $$\int_{\mathbf K} \bigl\| \tfrac{d}{ds} R(s)(k)\big|_{s = it} \bigr\|^2 \, dk \;\le\; \bigl(C\,(1 + D(t))^{A}\bigr)^2,$$
--   the integral being taken against `maximalCompactHaar K` and the derivative being the complex derivative of $s \mapsto R(s)(k)$ at the point $it$. The constants $C$ and $A$ are independent of $\mu$, $\nu$, the section family $\psi f$, the functions $E_\psi, N_\psi$, the parameters $\delta$ and $R$, and $t$.
--
--   This is the uniform $L^2(\mathbf K)$ bound, on the unitary axis $\operatorname{Re} s = 0$, for the $s$-derivative of the completed and normalised Weyl intertwining operator attached to a flat family of induced sections for $GL_2$ over a number field, with polynomial dependence on the archimedean parameters $\tau_\mu, \tau_\nu, m_\mu, m_\nu$ through $D(t)$. It feeds the construction of the axis continuation of the intertwining operator in [`AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat`](thm.html#AutomorphicForm.exists_forall_completedL_mul_axis_continuation_weylIntertwiningIntegral_eq_mul_normalizedIntertwining_and_lintegral_le_of_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat.lean

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

theorem AutomorphicForm.exists_forall_lintegral_norm_sq_deriv_normalizedIntertwining_axis_le_of_completedL_mul_weylIntertwiningIntegral_eq_of_flat
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
      ∀ t : ℝ, (∫ k, ‖deriv (fun s : ℂ => R s k) ((t : ℂ) * Complex.I)‖ ^ 2 ∂(maximalCompactHaar K)) ≤ (C * (1 + D t) ^ A) ^ 2 := by sorry
