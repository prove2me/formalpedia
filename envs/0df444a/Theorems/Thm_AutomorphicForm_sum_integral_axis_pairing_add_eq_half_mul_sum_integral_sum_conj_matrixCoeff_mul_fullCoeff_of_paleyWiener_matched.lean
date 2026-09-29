-- Prove2me | Theorems.Thm_AutomorphicForm_sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched
-- name    : AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/2a10f3eb-304b-5a05-b62f-262ae2279c50
-- title:
--   Symmetric fold of the Eisenstein axis pairing
-- statement:
--   Throughout, $K$ is a number field, $\mathbb{A}=$ `AdeleRing (𝓞 K) K` its adele ring, $G=$ `AdelicGL2 (𝓞 K) K` $=\mathrm{GL}_2(\mathbb{A})$, $\mathbf{K}=$ `adelicMaximalCompact K` the subgroup of those $g$ whose finite part lies in `finiteIntegralGL2 (𝓞 K) K` and whose component at each infinite place is a row isometry, and $dk$ denotes `maximalCompactHaar K`, the Haar measure of $\mathbf{K}$. Integrals over $\mathbb{R}$ are with respect to Lebesgue measure. Write $v$ for the real number `((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal`, the additive Haar volume of the adelic box (the product of a fundamental domain for the Minkowski lattice at the infinite places with the integral finite adeles), regarded as a complex number, and $v^{-1}$ for its inverse. For a test function $f$ on $G$, `convOp K f u = rightConv K u f` is the right convolution $g \mapsto \int_G u(gx) f(x)\,dx$ against the Haar measure `adelicGLHaar (Fin 2) (𝓞 K) K` of $G$.
--
--   Fixed data and hypotheses on the global character. Real numbers $\alpha,\beta$ with $0<\alpha$ (`hα`) and $\alpha<\beta$ (`hαβ`); a finite set $S_K$ of height-one primes of $\mathcal{O}_K$; a homomorphism $\xi_K$ from the full subgroup $\top$ of $\mathbb{A}^\times$ to $\mathbb{C}^\times$ which is continuous as a $\mathbb{C}$-valued function on $\mathbb{A}^\times$ (`hξc`), trivial on the image of $K^\times$ (`hξt`) and unitary, $\|\xi_K(z)\|=1$ (`hξu`); an ideal $N$ of $\mathcal{O}_K$ such that every prime dividing $N$ belongs to $S_K$ (`hN`); and an archimedean type family $\mathrm{tys}_K$ `: ArchTypeFamily K`, i.e. a finite list of representations of the row-isometry group at each infinite place, which cuts out the submodules `archCutSubmodule K tysK` and `archDualCutSubmodule K tysK`.
--
--   The modulus character. $\alpha_m : \mathbb{A}^\times \to \mathbb{R}^\times$ is obtained from the distributive Haar character of $\mathbb{A}$ composed with $\mathbb{R}_{\ge 0} \to \mathbb{R}$, passed to units; the hypothesis `hαm` asserts $\alpha_m(x)>0$ for all $x$. For characters $\mu,\nu$ and $s \in \mathbb{C}$, `etaFst μ αm hαm s` $=\mu\cdot \alpha_m^{\,s+1/2}$ and `etaSnd ν αm hαm s` $=\nu\cdot\alpha_m^{-(s+1/2)}$, where $\alpha_m^{\,w}(x)=\alpha_m(x)^w$ as a complex power. A function $\varphi$ on $G$ is an induced section for a pair $(\chi_1,\chi_2)$ when $\varphi(bg)=\chi_1(b_{11})\chi_2(b_{22})\varphi(g)$ for every $b$ in the adelic Borel subgroup (lower left entry zero) and every $g$.
--
--   The continuous (Eisenstein) block. A countable type $\iota_E$, families of characters $\mu,\nu : \iota_E \to \mathrm{Hom}(\mathbb{A}^\times,\mathbb{C}^\times)$ subject to: unitarity (`_hμ`, `_hν`), triviality on $K^\times$ (`_hμic`, `_hνic`), continuity (`_hμc`, `_hνc`), the product relation $\mu_e(z)\nu_e(z)=\xi_K(z)$ for all $e$ and all $z$ (`_hμν`), and separation: distinct indices are separated by a norm-one idele, i.e. an element of the kernel of the distributive Haar character, at which $\mu$ or $\nu$ differ (`_hdist`). Further, integers $n_E(e)$ and functions $\varphi_E(e,j,s) : G \to \mathbb{C}$ for $j < n_E(e)$, $s\in\mathbb{C}$, subject to the following groups of hypotheses: each $\varphi_E(e,j,s)$ is an induced section for $(\mathrm{etaFst}(\mu_e),\mathrm{etaSnd}(\nu_e))$ at $s$ (`_hφE`), is archimedean $K$-finite (`_hφEK`) and $K_f$-smooth, i.e. a smooth vector for the kernel of the archimedean projection (`_hφEf`); the map $(s,g)\mapsto \varphi_E(e,j,s)(g)$ is continuous (`_hφEjc`) and holomorphic in $s$ for each $g$ (`_hφEhol`); at each infinite place the right translates under the archimedean row-isometry subgroup lie in one finite-dimensional space, uniformly in $s$ and $g$ (`_hφEKu`); on $\mathbf{K}$ the sections are flat, $\varphi_E(e,j,s)(k)=\varphi_E(e,j,0)(k)$ (`_hφEflat`); they are right invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` (`_hφElev`) and lie in `archCutSubmodule K tysK` (`_hφEty`); they are orthonormal, $\int_{\mathbf{K}} \varphi_E(e,i,0)(k)\overline{\varphi_E(e,j,0)(k)}\,dk = \delta_{ij}$ (`_hφEon`); and they span: for each $e$, each $t\in\mathbb{R}$ and each $\varphi_0$ which is an induced section at $s=it$ for the same characters, continuous, archimedean $K$-finite, right invariant under the above level subgroup and in `archCutSubmodule K tysK`, $\varphi_0$ lies in the complex span of the $\varphi_E(e,j,it)$, $j<n_E(e)$ (`_hφEspan`).
--
--   Axis continuations of the Eisenstein block. Sets $O_E(e,j)\subseteq\mathbb{C}$ and functions $E_E, N_E$ with the nine-clause hypothesis `_hEE`: $O_E(e,j)$ is open, preconnected, contains the imaginary axis $\{\mathrm{Re}\,s=0\}$ and the half-plane $\{\mathrm{Re}\,s>1/2\}$; for each $g$ the functions $s\mapsto E_E(e,j,s)(g)$ and $s\mapsto N_E(e,j,s)(g)$ are analytic on a neighbourhood of $O_E(e,j)$; both $(s,g)\mapsto E_E$ and $(s,g)\mapsto N_E$ are continuous on $O_E(e,j)\times G$; and for $\mathrm{Re}\,s>1/2$ one has $E_E(e,j,s)(g)=\varphi_E(e,j,s)(g)+\sum_{\xi\in K}\varphi_E(e,j,s)(w\,u(\xi)\,g)$, with $w$ the adelic Weyl element and $u(\xi)$ the upper unipotent matrix, and $N_E(e,j,s)(g)$ equals the Weyl intertwining integral $\int_{\mathbb{A}}\varphi_E(e,j,s)(w^{-1}u(x)g)\,dx$ against `adelicAddHaar (𝓞 K) K`.
--
--   The test function. $f : G \to \mathbb{C}$ continuous (`_hf`) with compact support (`_hfc`), factorizable as $f(g)=f_\infty(\text{arch part of }g)\,f_{\mathrm{fin}}(\text{finite part of }g)$ with $f_\infty$ smooth in the matrix entries and compactly supported and $f_{\mathrm{fin}}$ locally constant and compactly supported, bi-invariant under `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, and archimedean bi-finite for $\mathrm{tys}_K$, i.e. $g\mapsto f(g^{-1})$ lies in `archCutSubmodule K tysK` and $f$ in `archDualCutSubmodule K tysK` (these three conditions are unnamed hypotheses).
--
--   The finite Paley–Wiener datum. A finite type $\iota_P$ with characters $\mu_P,\nu_P$ which are unitary, trivial on $K^\times$, and continuous (continuity of $\mu_P$ and of $\nu_P$ being separate hypotheses), satisfy $\mu_P(e)(z)\,\nu_P(e)(z)=\xi_K(z)$ for every $z$ in the group `Z` of `productionPinsOf K (canonicalTruncationDomain K α β) (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)`, which is the full group $\mathbb{A}^\times$, and are separated on norm-one ideles as in the $\iota_E$ block; a map $r_P : \iota_P\to\iota_P$ effecting an exact swap, $\mu_P(r_P e)=\nu_P(e)$ and $\nu_P(r_P e)=\mu_P(e)$ (`_hr`). Two families $\varphi_f,\psi_f : \iota_P\to\mathbb{C}\to G\to\mathbb{C}$, both consisting of induced sections for $(\mathrm{etaFst}(\mu_P(e)),\mathrm{etaSnd}(\nu_P(e)))$ at each $s$ (`_hφf`, `_hψf`), jointly continuous (`_hφjc`, `_hψjc`) and holomorphic in $s$ (`_hφhol`, `_hψhol`); $\psi_f$ is in addition archimedean $K$-finite (`_hψK`), $K_f$-smooth (`_hψsm`) and has uniformly finite-dimensional archimedean $K$-types (`_hψKu`). The vertical decay hypotheses `_hφdec` and `_hψdec` require, for each index, each $n\in\mathbb{N}$, each $\sigma_0\in\mathbb{R}$ and each compact $C\subseteq G$, an integrable bounded majorant $m:\mathbb{R}\to\mathbb{R}$ with $(1+|t|)^n\,\|\varphi_f(e,\sigma'+it)(g)\|\le m(t)$, respectively the same bound for $\psi_f$, for all $|\sigma'|\le\sigma_0$, all $t$ and all $g\in C$. Sets $O_\psi(i)$ and functions $E_\psi,N_\psi$ satisfy the hypothesis `_hEψ`, which is the nine-clause package `_hEE` above with $\varphi_E(e,j,\cdot)$ replaced by $\psi_f(i,\cdot)$.
--
--   Matching and growth on the axis. A map $em:\iota_P\to\iota_E$ and shifts $\tau:\iota_P\to\mathbb{R}$ with $\mu_P(i)=\mu(em\,i)\cdot \mathrm{normPowChar}_K(\tau_i)$ and $\nu_P(i)=\nu(em\,i)\cdot \mathrm{normPowChar}_K(\tau_i)^{-1}$, where $\mathrm{normPowChar}_K(\tau)(x)=\|x\|^{\,i\tau}$ is the idele-norm power character (`_hem`). Finally, polynomial growth on the unitary axis, uniformly on $\mathbf{K}$: for each $i$ there are $A\in\mathbb{R}$ and $n\in\mathbb{N}$ with $\|N_\psi(i,it)(k)\|\le A(1+|t|)^n$ for all $t\in\mathbb{R}$ and $k\in\mathbf{K}$ (`_hNψ`), and likewise for each $(e,j)$ with $N_E(e,j,it)(k)$ (`_hNE`).
--
--   Conclusion. Write $t_i := t+\tau_i$ and, for $X\in\{\varphi_f,\psi_f\}$ and $j<n_E(em\,i)$,
--   $$C^X_j(i,t) := \int_{\mathbf{K}} X(i,it)(k)\,\overline{\varphi_E(em\,i,j,it_i)(k)}\,dk \; + \; \int_{\mathbf{K}} X(r_P i,-it)(k)\,\overline{v^{-1}\,N_E(em\,i,j,it_i)(k)}\,dk,$$
--   $$A_{j k'}(i,t) := \int_{\mathbf{K}} \big(\mathrm{rightConv}\,\varphi_E(em\,i,k',it_i)\;f\big)(k)\,\overline{\varphi_E(em\,i,j,it_i)(k)}\,dk,$$
--   the first factor in $A_{jk'}$ being $g\mapsto \int_G \varphi_E(em\,i,k',it_i)(gx) f(x)\,dx$. Then
--   $$\sum_{i\in\iota_P}\int_{\mathbb{R}}\Big(\int_{\mathbf{K}} \varphi_f(i,it)(k)\,\overline{(\mathrm{convOp}\,f)\big(\psi_f(i,it)\big)(k)}\,dk \;+\; v^{-1}\int_{\mathbf{K}} \varphi_f(i,it)(k)\,\overline{(\mathrm{convOp}\,f)\big(N_\psi(r_P i,-it)\big)(k)}\,dk\Big)\,dt$$
--   $$=\;\tfrac12\sum_{i\in\iota_P}\int_{\mathbb{R}} \sum_{j<n_E(em\,i)}\;\sum_{k'<n_E(em\,i)} \overline{A_{j k'}(i,t)}\;\Big(C^{\varphi_f}_j(i,t)\cdot \overline{C^{\psi_f}_{k'}(i,t)}\Big)\,dt .$$
--   Here the sums over $\iota_P$ are finite sums over the whole index set and the $t$-integrals are over the whole line, the factor $1/2$ absorbing the double counting of the pairs $(i,t)$ and $(r_P i,-t)$.
--
--   This is the symmetric form of the spectral (Eisenstein) contribution to the trace-formula computation on $\mathrm{GL}_2$ over a number field: the left-hand side is the two-term pairing along the unitary axis of a weak Paley–Wiener family against the $f$-convolution of a strong one, and the right-hand side expresses it through matrix coefficients of $R(f)$ in the orthonormal level-$N$, fixed-type families of induced sections, with the constant-term (Weyl intertwining) contributions folded into the full coefficients $C^X_j$. It is obtained by symmetrising, under the re-indexing $(i,t)\mapsto (r_P i,-t)$, the asymmetric identity [`AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched`](thm.html#AutomorphicForm.axis_pairing_add_inv_vol_axis_pairing_weylIntertwining_eq_sum_conj_matrixCoeff_mul_inner_mul_conj_of_paleyWiener_matched), together with the integrability statement [`AutomorphicForm.integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched`](thm.html#AutomorphicForm.integrable_axis_pairing_convOp_add_inv_vol_axis_pairing_convOp_weylIntertwining_of_paleyWiener_matched) and the swap identity [`AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched`](thm.html#AutomorphicForm.sum_conj_matrixCoeff_mul_axis_pairing_weylIntertwining_mul_conj_fullCoeff_eq_axis_pairing_swap_neg_of_paleyWiener_matched), and is used by [`AutomorphicForm.conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener`](thm.html#AutomorphicForm.conj_sum_integral_axis_pairing_add_eq_mul_tsum_integral_sum_rightConv_mul_thetaPairing_of_matched_paleyWiener).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched.lean

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

theorem AutomorphicForm.sum_integral_axis_pairing_add_eq_half_mul_sum_integral_sum_conj_matrixCoeff_mul_fullCoeff_of_paleyWiener_matched
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
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
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
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
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n),
    ∑ i : ιP, ∫ t : ℝ,
      ((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (ψf i ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
        (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * ∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (convOp K f (Nψ (rP i) (-((t : ℂ) * Complex.I))) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
    (1 / 2 : ℂ) * ∑ i : ιP, ∫ t : ℝ,
      ∑ j : Fin (nE (em i)), ∑ k' : Fin (nE (em i)),
        conj (∫ k, rightConv K (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I)) f (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))
              ∂(maximalCompactHaar K)) *
        (((∫ k, φf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, φf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) j (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          conj ((∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) +
            ∫ k, ψf (rP i) (-((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 K) K) * conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) := by sorry
