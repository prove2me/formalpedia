-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
-- name    : AutomorphicForm.exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/756c756f-100f-5af0-9992-5df9166ae20e
-- title:
--   Integrability of the truncated σ-twisted continuous spectral expansion
-- statement:
--   Setting. Let $K$ and $L$ be number fields with $L$ an algebra over $K$, and write $\mathbb{A}_L$ for the adele ring of $L$ and $\mathrm{GL}_2(\mathbb{A}_L)$ for `AdelicGL2 (𝓞 L) L`. Let $\alpha,\beta$ be reals with $0<\alpha$ and $\alpha<\beta$, and call the *slab* the set of $g$ with $\|\det g\|_{\mathbb{A}_L}\in[\alpha,\beta]$, the norm being [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19), i.e. the value of the distributive Haar character of $\mathbb{A}_L$. A set $\Phi_L\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ is given which is contained in the slab (`hΦs`) and is a fundamental domain, in the sense of `IsFundamentalDomain`, for the image of $\mathrm{GL}_2(L)$ under `globalPoints` acting on the adelic Haar measure `adelicGLHaar` restricted to the slab (`hΦ`). On the idele group $\mathbb{A}_L^\times$ a measurable space and Borel structure are fixed, $\nu_{Z,L}$ is a Haar measure on $\mathbb{A}_L^\times$ and $\Omega_L$ is a fundamental domain for the image of $L^\times$ in $\mathbb{A}_L^\times$ with respect to $\nu_{Z,L}$ (`hΩL`). Further data: an idele Galois descent datum $D$ for $(\mathcal{O}_L,K,L)$, that is, a homomorphism from $\mathrm{Aut}_K(L)$ to the ring automorphisms of $\mathbb{A}_L$ compatible with the embedding of $L$ and continuous in each automorphism; an element $\sigma\in L\simeq_{\mathrm{alg}[K]}L$; a finite set $S_L$ of finite places of $L$; a homomorphism $\xi$ from the full subgroup of $\mathbb{A}_L^\times$ to $\mathbb{C}^\times$ which is continuous (`hξc`), trivial on the principal ideles (`hξt`) and of modulus one at every idele (`hξu`); an ideal $N\subseteq\mathcal{O}_L$ all of whose prime divisors lie in $S_L$ (`hN`); and an archimedean type family `tysL`, i.e. for each infinite place $w$ of $L$ a finite list of representations of the row-isometry subgroup at $w$.
--
--   Siegel data. Reals $c,u,d_1,d_2$ with $0<c$ (`hc`), a compact set $T_c\subseteq\mathrm{GL}_2(\mathbb{A}_L)$ (`hTc`), and a set $\Phi_0$ which is contained in the union over $y\in T_c$ of the right translates $(\,\cdot\,y)$ of the centre-cut Siegel set `WindowedSiegel.centreCutSiegelSet L c u d₁ d₂` — the set of $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose window invariant `xWindowSq` is at most $u^2$ at every infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$ (`hΦ₀S`) — which is contained in the slab (`hΦ₀s`) and which is itself a fundamental domain for the image of $\mathrm{GL}_2(L)$ for the Haar measure restricted to the slab (`hΦ₀`).
--
--   The modulus character. Put $\alpha_m:\mathbb{A}_L^\times\to\mathbb{R}^\times$ for the homomorphism obtained from the distributive Haar character of $\mathbb{A}_L$ through $\mathbb{R}_{\ge0}\to\mathbb{R}$, the Borel structure `adeleBorel` being used on $\mathbb{A}_L$; the hypothesis `hαm` states that all values of $\alpha_m$ are positive. For a character $\chi$ and $s\in\mathbb{C}$ the twists `etaFst χ αm hαm s` $=\chi\cdot\alpha_m^{s+1/2}$ and `etaSnd χ αm hαm s` $=\chi\cdot\alpha_m^{-(s+1/2)}$ are formed with complex powers of $\alpha_m$.
--
--   Eisenstein data. A countable type $\iota_E$ and families $\mu,\nu:\iota_E\to\mathrm{Hom}(\mathbb{A}_L^\times,\mathbb{C}^\times)$ are given, subject to: each $\mu_e,\nu_e$ is of modulus one everywhere (`_hμ`, `_hν`), trivial on $L^\times$ (`_hμic`, `_hνic`), continuous (`_hμc`, `_hνc`), with $\mu_e(z)\nu_e(z)=\xi(z)$ for all $z$ (`_hμν`), and with distinct indices separated on the norm-one ideles: for $e\neq e'$ there is $z$ in the kernel of the distributive Haar character with $\mu_e(z)\neq\mu_{e'}(z)$ or $\nu_e(z)\neq\nu_{e'}(z)$ (`_hdist`).
--
--   Sections. Integers $n_E(e)$ and functions $\varphi_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ for $j\in\mathrm{Fin}(n_E(e))$ are given, with the following hypotheses: each $\varphi_{e,j}(s,\cdot)$ is an induced section for the pair $(\,$`etaFst (μ e) … s`$,\,$`etaSnd (ν e) … s`$)$, i.e. $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for every $b$ in the adelic Borel subgroup (`_hφE`); archimedean $K$-finiteness (`_hφEK`); smoothness as a vector for the finite-adelic subgroup, the kernel of the archimedean projection (`_hφEf`); joint continuity in $(s,g)$ (`_hφEjc`); complex differentiability in $s$ for each $g$ (`_hφEhol`); a uniform $K$-type bound at each infinite place $w$: a finite-dimensional subspace $W$ of functions on the archimedean row-isometry subgroup at $w$ containing all right translates $k\mapsto\varphi_{e,j}(s,gk)$ (`_hφEKu`); flatness on the adelic maximal compact, $\varphi_{e,j}(s,k)=\varphi_{e,j}(0,k)$ (`_hφEflat`); right invariance under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L` (`_hφElev`); membership in the archimedean cut submodule of types `tysL`, the intersection over infinite places of the sums of the prescribed type submodules (`_hφEty`); orthonormality $\int_{K}\varphi_{e,i}(0,k)\overline{\varphi_{e,j}(0,k)}\,d\,$`maximalCompactHaar`$=\delta_{ij}$ (`_hφEon`); spanning (`_hφEspan`): for each $e$, each real $t$ and each $\varphi_0$ which is an induced section at $s=it$ for the pair attached to $(\mu_e,\nu_e)$, continuous, archimedean $K$-finite, invariant under the level subgroup and of types `tysL`, the function $\varphi_0$ lies in the complex span of the $\varphi_{e,j}(it,\cdot)$; and exhaustiveness of the pairs (`_hpairs`): for every pair $(\mu',\nu')$ of continuous characters of modulus one, trivial on $L^\times$, with $\mu'\nu'=\xi$, every real $t$ and every non-zero $\varphi_0$ with the same five properties at $s=it$, there is an index $e$ with $\mu_e=\mu'$ and $\nu_e=\nu'$ on the norm-one ideles.
--
--   Continuations. Sets $O_{e,j}\subseteq\mathbb{C}$ and families $E_{e,j},N_{e,j}:\mathbb{C}\times\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ are given, with the hypothesis `_hEE` (nine clauses) stating, for all $e,j$: $O_{e,j}$ is open and preconnected and contains both the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_{e,j}(s,g)$ and $s\mapsto N_{e,j}(s,g)$ are analytic on a neighbourhood of $O_{e,j}$; both $(s,g)\mapsto E_{e,j}(s,g)$ and $(s,g)\mapsto N_{e,j}(s,g)$ are continuous on $O_{e,j}\times\mathrm{GL}_2(\mathbb{A}_L)$; for $\mathrm{Re}\,s>1/2$, $E_{e,j}(s,g)=\varphi_{e,j}(s,g)+\sum_{\xi\in L}\varphi_{e,j}\bigl(s,\,w\,n(\xi)\,g\bigr)$ with $w=$`adelicWeyl` and $n(\xi)$ the unipotent matrix with upper entry the image of $\xi$; and for $\mathrm{Re}\,s>1/2$, $N_{e,j}(s,g)$ is the Weyl intertwining integral $\int_{\mathbb{A}_L}\varphi_{e,j}(s,w^{-1}n(x)g)\,dx$ for the adelic additive Haar measure.
--
--   Test function. Finally $f:\mathrm{GL}_2(\mathbb{A}_L)\to\mathbb{C}$ is continuous (`_hf`) with compact support (`_hfc`), factorizable (a product of a smooth compactly supported archimedean factor in the matrix entries with a locally constant compactly supported finite factor), bi-invariant under `principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L`, and archimedean bi-finite of types `tysL`, i.e. $g\mapsto f(g^{-1})$ lies in the archimedean cut submodule and $f$ in the archimedean dual cut submodule of `tysL`.
--
--   Truncation. For a real parameter $R$ write $\Lambda^{R}$ for the truncation operator [`AutomorphicForm.lambdaT`](def/AutomorphicForm_TruncationOperator.html#L48) at height $\exp R$, formed with the measurable space and measure fields of the record `productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun w => heckeGen (𝓞 L) L w) (adelicBox L)` — namely the Borel structure on $\mathbb{A}_L$ and the adelic additive Haar measure conditioned on the adelic box of $L$ — with the unipotent embedding $t\mapsto$ `unipotentGL2 t` and the height function [`NumberField.AdelicHeight.adelicHeight L`](def/NumberField_AdelicHeight.html#L158); thus $\Lambda^{R}\psi(g)=\psi(g)-\mathbf{1}_{\{\,\exp R<\mathrm{ht}(g)\,\}}(g)\cdot\psi^{\mathrm{const}}(g)$, where $\psi^{\mathrm{const}}$ is the constant term of $\psi$ along the unipotent for that measure. Write $\sigma_{\mathbb{A}}^{-1}$ for [`AutomorphicForm.sigmaAdelicAct K L D σ.symm`](def/AutomorphicForm_SigmaAdelicAction.html#L14), the map on $\mathrm{GL}_2(\mathbb{A}_L)$ induced entrywise by $D.\mathrm{act}(\sigma^{-1})$.
--
--   Conclusion. There exists $R_0\in\mathbb{R}$ such that for every $R\ge R_0$ the following three assertions hold, where for $e\in\iota_E$ and $p=(t,g)\in\mathbb{R}\times\mathrm{GL}_2(\mathbb{A}_L)$ the integrand is
--   $$F_e(p)=\sum_{i}\sum_{j}\Bigl(\int_{K}\bigl(\mathrm{rightConv}\,L\ \varphi_{e,j}(it,\cdot)\ f\bigr)(k)\,\overline{\varphi_{e,i}(it,k)}\,d\,\mathrm{maximalCompactHaar}\,L\Bigr)\cdot\Bigl(E_{e,i}(it,g)\cdot\overline{\Lambda^{R}\bigl(E_{e,j}(it,\sigma_{\mathbb{A}}^{-1}(\cdot))\bigr)(g)}\Bigr),$$
--   the inner integral being over the adelic maximal compact subgroup and `rightConv L φ f (g)` $=\int\varphi(gx)f(x)\,d\,$`adelicGLHaar`:
--
--   (i) for every $e\in\iota_E$ the function $F_e$ is integrable on $\mathbb{R}\times\mathrm{GL}_2(\mathbb{A}_L)$ for the product of Lebesgue measure on $\mathbb{R}$ with `adelicGLHaar` restricted to $\Phi_0$;
--
--   (ii) the family $e\mapsto\int\|F_e(p)\|\,dp$, for the same product measure, is summable over $\iota_E$;
--
--   (iii) for every $e$, all $i,j\in\mathrm{Fin}(n_E(e))$ and every real $t$, both of the following functions of $x$ are integrable on $\Phi_0$ for `adelicGLHaar`: the product $\Lambda^{R}\bigl(E_{e,j}(it,\sigma_{\mathbb{A}}^{-1}(\cdot))\bigr)(x)\cdot\overline{E_{e,i}(it,x)}$, and the product $\Lambda^{R}\bigl(E_{e,j}(it,\sigma_{\mathbb{A}}^{-1}(\cdot))\bigr)(x)\cdot\overline{\Lambda^{R}\bigl(E_{e,i}(it,\cdot)\bigr)(x)}$, the truncation in the second factor of the latter being applied to the untwisted continuation $E_{e,i}(it,\cdot)$.
--
--   This is the convergence input for the continuous-spectrum contribution to the $\sigma$-twisted trace formula for $\mathrm{GL}_2$ over a number field $L$ with a unitary central character: it asserts absolute integrability, over the product of the spectral parameter line with a Siegel-type fundamental domain, of the truncated Eisenstein bilinear expansion read along the Galois-twisted diagonal, together with summability over the countable family of Eisenstein data and integrability of the individual truncated pairings. It is used by the statement that evaluates the integral of the twisted truncated kernel against this expansion, on the route to base change for $\mathrm{GL}_2$ and the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Mathlib.MeasureTheory.Measure.Prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_forall_integrable_prod_sum_rightConv_mul_axis_continuation_mul_conj_lambdaT_sigmaAdelicAct_symm_of_subset_iUnion_image_centreCutSiegelSet
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (νZL : Measure (AdeleRing (𝓞 L) L)ˣ) [νZL.IsHaarMeasure] (ΩL : Set (AdeleRing (𝓞 L) L)ˣ)
    (hΩL : IsFundamentalDomain
      (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range ΩL νZL)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (SL : Finset (HeightOneSpectrum (𝓞 L))) (ξu : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 L) L)ˣ,
      z ∈ (Units.map (algebraMap L (AdeleRing (𝓞 L) L) : L →* AdeleRing (𝓞 L) L)).range →
        ξu ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (c u d₁ d₂ : ℝ) (hc : 0 < c)
    (Tc : Set (AdelicGL2 (𝓞 L) L)) (hTc : IsCompact Tc) (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀S : Φ₀ ⊆ ⋃ y ∈ Tc, (· * y) '' WindowedSiegel.centreCutSiegelSet L c u d₁ d₂)
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hξu : ∀ z : (AdeleRing (𝓞 L) L)ˣ, ‖((ξu ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits
    letI := adeleBorel (𝓞 L) L
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 L) L)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 L) L (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 L) L (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 L) L (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 L) L (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 L) L)ˣ), μ e z * ν e z = ξu ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles L,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite L (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth L (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 L) L => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 L) L), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace L), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
          (fun k : ↥(archRowIsometrySubgroup L w) => φE e j s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact L),
        φE e j s (k : AdelicGL2 (𝓞 L) L) = φE e j 0 (k : AdelicGL2 (𝓞 L) L))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule L tysL)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 L) L) * conj (φE e j 0 (k : AdelicGL2 (𝓞 L) L)) ∂(maximalCompactHaar L) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 L) L μ' → IsUnitaryChar (𝓞 L) L ν' →
        IsIdeleClassChar (𝓞 L) L μ' → IsIdeleClassChar (𝓞 L) L ν' →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 L) L)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 L) L)ˣ, μ' z * ν' z = ξu ⟨z, Subgroup.mem_top z⟩) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 L) L → ℂ),
        IsInducedSection (𝓞 L) L (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite L φ₀ →
        (∀ (g : AdelicGL2 (𝓞 L) L), ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule L tysL → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles L, μ e z = μ' z ∧ ν e z = ν' z)
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 L) L → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        EE e j s g = φE e j s g + ∑' ξ : L, φE e j s (adelicWeyl (𝓞 L) L
          * unipotentGL2 (algebraMap L (AdeleRing (𝓞 L) L) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        NE e j s g = weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (φE e j s) g))
      (f : AdelicGL2 (𝓞 L) L → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn L f →
      IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f →
      IsArchBiFinite L tysL f →
    ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      (∀ e : ιE, Integrable (fun p : ℝ × AdelicGL2 (𝓞 L) L => ∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                p.2))))
          ((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀))) ∧
      (Summable fun e : ιE => ∫ p : ℝ × AdelicGL2 (𝓞 L) L, ‖∑ i : Fin (nE e), ∑ j : Fin (nE e),
          (∫ k, rightConv L (φE e j ((p.1 : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 L) L) * conj (φE e i ((p.1 : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 L) L))
              ∂(maximalCompactHaar L)) *
            (EE e i ((p.1 : ℂ) * Complex.I) p.2 *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((p.1 : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                p.2)))‖
          ∂((volume : Measure ℝ).prod ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict Φ₀))) ∧
      (∀ (e : ιE) (i j : Fin (nE e)) (t : ℝ),
        IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x) *
              conj (EE e i ((t : ℂ) * Complex.I) x))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ∧
        IntegrableOn (fun x : AdelicGL2 (𝓞 L) L =>
              (@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (fun y => EE e j ((t : ℂ) * Complex.I) (AutomorphicForm.sigmaAdelicAct K L D σ.symm y))
                x) *
              conj ((@AutomorphicForm.lambdaT _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).nS _ _
                (productionPinsOf L ΦL (fun M => levelOne (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
                  (fun w => heckeGen (𝓞 L) L w) (adelicBox L)).ν
                (fun t => AutomorphicForm.unipotentGL2 t)
                (NumberField.AdelicHeight.adelicHeight L) (Real.exp R)
                (EE e i ((t : ℂ) * Complex.I))
                x)))
          Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) := by sorry
