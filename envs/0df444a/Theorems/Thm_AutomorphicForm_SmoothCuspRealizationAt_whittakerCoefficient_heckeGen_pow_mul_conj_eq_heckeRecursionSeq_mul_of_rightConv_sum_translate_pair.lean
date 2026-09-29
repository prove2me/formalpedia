-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
-- name    : AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/8d293bdb-634c-5d58-8922-86282f0a79b2
-- title:
--   Paired Whittaker coefficients follow the Hecke recursion at good places
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be real numbers, let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$ (written `AdelicGL2 (𝓞 K) K`), and let $S$, $S_\psi$ be finite sets of finite places of $K$ with $S_\psi\subseteq S$ and such that for every $v\notin S_\psi$ the level `addCharLevel` of the local character `psiLocal K v` is $0$.
--
--   All Whittaker coefficients below are taken with respect to the carrier data `productionPinsOf K D U gen (adelicBox K)`, where $D=\bigcup_{x\in T}\{g x: g\in\;$`centreCutSiegelSet K c u d₁ d₂`$\}$ is the union of the right translates by elements of $T$ of the centre-cut Siegel set (those $g$ whose finite part is integral with integral inverse, whose local height at each infinite place is at least $c$, whose window quantity `xWindowSq` is at most $u^2$ at each infinite place, and whose archimedean determinant norms all lie in $[d_1,d_2]$), where $U(N)=$ `levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K` is the level-$N$ congruence subgroup intersected with the kernel of the archimedean projection, where `gen v = heckeGen (𝓞 K) K v` is the Hecke generator at $v$, and where the group is given its Borel structure and Haar measure, the central subgroup is all of $(\mathbb{A}_K)^\times$, and the additive measure is the adelic additive Haar measure conditioned on the adelic box `adelicBox K`. Thus, for a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_K)$, $\alpha\in K$ and $g$, the quantity `whittakerCoefficient` is $\int \varphi(u(x)g)\,\psi(-\alpha x)\,d\nu(x)$, with $u(x)$ the upper unipotent matrix with entry $x$, and $\psi=$ [`NumberField.StandardAddChar.stdAddChar K`](def/NumberField_AdelicTraceFin.html#L198) the standard global additive character.
--
--   For $i=1,2$ the data are: a Hecke eigensystem $\Theta_i$ over $\mathbb{C}$ (a nonzero level ideal $\Theta_i.\mathrm{level}$ together with parameter functions $a,b$ on finite places), and a smooth cuspidal realization $R_i$ at the above carrier data for the renormalised eigensystem $\Theta_i$`.toRawCentral`, whose level and $a$-parameters are those of $\Theta_i$ and whose $b$-parameter at $v$ is $(\#(\mathcal{O}_K/v))^{-1}\Theta_i.b(v)$; so $R_i$ is a nonzero function with a central character, smooth and cuspidal at the carrier data, invariant under right translation by $U(\Theta_i.\mathrm{level})$, with a finite exceptional set outside which it is a Hecke coset eigenfunction at `heckeGen v` with eigenvalue $\Theta_i.a(v)$ and satisfies the central-uniformizer law with eigenvalue $(\#(\mathcal{O}_K/v))^{-1}\Theta_i.b(v)$.
--
--   The hypotheses attached to each index $i$ are: `_hRᵢ`, asserting that $R_i$ is a genuine realization, i.e. that $R_i$ is continuous; `_hRlevᵢ`, right invariance of $R_i$ under `levelOne (𝓞 K) K Θᵢ.level ⊓ finiteAdelicGL2Subgroup K`; a test function $f_i:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with `_hfTᵢ` asserting that $f_i$ is factorizable, that is, a product of a compactly supported smooth archimedean factor and a compactly supported locally constant finite factor; a finite set $S_{f_i}\subseteq S$ and the support condition `_hfsuppᵢ`, requiring of every $z$ with $f_i(z)\neq 0$ both that the $v$-component of the finite part of $z$ lie in `localIntegralSet K v` for all $v\notin S_{f_i}$, and that $z$ factor as $z=z_1z_2$ with $z_2\in$ `levelOne (𝓞 K) K Θᵢ.level ⊓ finiteAdelicGL2Subgroup K` and with $z_1$ commuting with [`UnramifiedWhittaker.placeEmbed K v xv`](def/UnramifiedWhittaker_HeckeRecursion.html#L47) for every $v\notin S_{f_i}$ and every $x_v\in\mathrm{GL}_2(K_v)$; and `_hSᵢ`, requiring that for $v\notin S$ the prime $v$ does not divide $\Theta_i.\mathrm{level}$ and does not lie in $R_i$`.exceptionalSet`.
--
--   Further, for each $i$ there are a natural number $r_i$, elements $h_i(1),\dots,h_i(r_i)$ of $\mathrm{GL}_2(\mathbb{A}_K)$ and complex coefficients $cs_i$, with `_hharchᵢ` asserting that each $h_i(j)$ has trivial archimedean part and `_hhcommᵢ` that each $h_i(j)$ commutes with the image of $\mathrm{GL}_2(K_v)$ under `placeEmbed K v` for every $v\notin S$; and a function $x_i$ on $\mathrm{GL}_2(\mathbb{A}_K)$ subject to four conditions: `_hxsumᵢ`, that $x_i(g)=\sum_j cs_i(j)\,(R_i * f_i)(g\,h_i(j))$, where $(R_i*f_i)(y)=\int R_i(yz) f_i(z)\,dz$ against the adelic Haar measure on $\mathrm{GL}_2$; `_hxintᵢ`, that for every $\alpha'\in K$ and every $g$ the integrand defining the Whittaker coefficient of $x_i$ at $(\alpha',g)$ is integrable for the conditioned additive measure; `_hxperᵢ`, that $x_i(u(\beta+u')h)=x_i(u(u')h)$ for all $\beta\in K$, all adeles $u'$ and all $h$; and `_hxZᵢ`, that $x_i(\mathrm{diag}(z,z)g)=R_i.\mathrm{centralChar}(z)\,x_i(g)$ for every idele unit $z$.
--
--   Finally, let $v$ be a finite place with $v\notin S$, let $k_1,k_2\in\mathrm{GL}_2(\mathbb{A}_K)$ have trivial finite part, let $g\in\mathrm{GL}_2(\mathbb{A}_K)$ satisfy the shell condition `_hg` that the $v$-adic valuation of the finite part of $\det g$ equals the square of the maximum of the $v$-adic valuations of the finite parts of the entries $g_{10}$ and $g_{11}$, and let $m$ be a natural number.
--
--   The conclusion is the identity
--   $$W_1\!\left(\varpi_v^{\,m} g k_1\right)\cdot\overline{W_2\!\left(\varpi_v^{\,m} g k_2\right)} = u_m\bigl(\Theta_1.a(v),\,\Theta_1.\mathrm{toRawCentral}.b(v)\bigr)\; u_m\bigl(\overline{\Theta_2.a(v)},\,\overline{\Theta_2.\mathrm{toRawCentral}.b(v)}\bigr)\;W_1(g k_1)\,\overline{W_2(g k_2)},$$
--   where $W_i(\cdot)$ denotes the Whittaker coefficient of $x_i$ at $\alpha=1$ for the standard additive character and the carrier data above, $\varpi_v=$ `heckeGen (𝓞 K) K v`, the bar is complex conjugation, and $u_m(\lambda,\omega)=$ [`UnramifiedWhittaker.heckeRecursionSeq N λ ω m`](def/UnramifiedWhittaker_HeckeRecursion.html#L11) with $N=\#(\mathcal{O}_K/v)$ the absolute norm of $v$, so that $u_0=1$, $u_1=\lambda/N$ and $u_{m+2}=(\lambda u_{m+1}-\omega u_m)/N$. Here $\Theta_i.\mathrm{toRawCentral}.b(v)=N^{-1}\Theta_i.b(v)$.
--
--   This is the unramified local Hecke computation in the pair form needed for Rankin–Selberg work: the product of the first Whittaker coefficient of one smoothed cusp form and the conjugate of that of a second, evaluated along the powers of the Hecke generator at a good place $v$ over a point of the zeroth Iwasawa shell, is the corresponding product of Hecke recursion values times the value at $m=0$. It is used in the growth estimates for class sums and in the construction of test data with nonvanishing Rankin–Selberg partial integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicBox NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering AutomorphicForm.SmoothCusp IsDedekindDomain

theorem AutomorphicForm.SmoothCuspRealizationAt.whittakerCoefficient_heckeGen_pow_mul_conj_eq_heckeRecursionSeq_mul_of_rightConv_sum_translate_pair
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (S Sψ : Finset (HeightOneSpectrum (𝓞 K))) (_hSψ : Sψ ⊆ S)
    (_hSψ0 : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sψ →
      LanglandsTunnell.TateLocal.addCharLevel (NumberField.StandardAddChar.psiLocal K v) = 0)
    (Θ₁ : HeckeEigensystem K ℂ)
    (R₁ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₁.toRawCentral)
    (_hR₁ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₁.toRawCentral R₁)
    (_hRlev₁ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ₁.level ⊓ finiteAdelicGL2Subgroup K,
      R₁.toFun (g * k) = R₁.toFun g)
    (f₁ : AdelicGL2 (𝓞 K) K → ℂ) (_hfT₁ : IsFactorizableTestFn K f₁)
    (Sf₁ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf₁ : Sf₁ ⊆ S)
    (_hfsupp₁ : ∀ z : AdelicGL2 (𝓞 K) K, f₁ z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₁ →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ₁.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₁ → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS₁ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ₁.level ∧ v ∉ R₁.exceptionalSet)
    (r₁ : ℕ) (h₁ : Fin r₁ → AdelicGL2 (𝓞 K) K) (cs₁ : Fin r₁ → ℂ)
    (_hharch₁ : ∀ i, glArch (𝓞 K) K (h₁ i) = 1)
    (_hhcomm₁ : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h₁ i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h₁ i)
    (x₁ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum₁ : ∀ g, x₁ g = ∑ i, cs₁ i * rightConv K R₁.toFun f₁ (g * h₁ i))
    (_hxint₁ : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x₁ α' g)
    (_hxper₁ : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x₁ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x₁ (unipotentGL2 uu * hh))
    (_hxZ₁ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x₁ (centralScalar (𝓞 K) K z * g) = ((R₁.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x₁ g)
    (Θ₂ : HeckeEigensystem K ℂ)
    (R₂ : SmoothCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₂.toRawCentral)
    (_hR₂ : IsGenuineCuspRealizationAt K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) Θ₂.toRawCentral R₂)
    (_hRlev₂ : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K Θ₂.level ⊓ finiteAdelicGL2Subgroup K,
      R₂.toFun (g * k) = R₂.toFun g)
    (f₂ : AdelicGL2 (𝓞 K) K → ℂ) (_hfT₂ : IsFactorizableTestFn K f₂)
    (Sf₂ : Finset (HeightOneSpectrum (𝓞 K))) (_hSf₂ : Sf₂ ⊆ S)
    (_hfsupp₂ : ∀ z : AdelicGL2 (𝓞 K) K, f₂ z ≠ 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₂ →
        finComponent (𝓞 K) K v (glFin (𝓞 K) K z) ∈ localIntegralSet K v) ∧
      ∃ z₁ z₂ : AdelicGL2 (𝓞 K) K, z = z₁ * z₂ ∧
        z₂ ∈ levelOne (𝓞 K) K Θ₂.level ⊓ finiteAdelicGL2Subgroup K ∧
        ∀ v : HeightOneSpectrum (𝓞 K), v ∉ Sf₂ → ∀ xv : GL (Fin 2) (v.adicCompletion K),
          z₁ * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * z₁)
    (_hS₂ : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ¬ v.asIdeal ∣ Θ₂.level ∧ v ∉ R₂.exceptionalSet)
    (r₂ : ℕ) (h₂ : Fin r₂ → AdelicGL2 (𝓞 K) K) (cs₂ : Fin r₂ → ℂ)
    (_hharch₂ : ∀ i, glArch (𝓞 K) K (h₂ i) = 1)
    (_hhcomm₂ : ∀ i, ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ xv : GL (Fin 2) (v.adicCompletion K),
      h₂ i * UnramifiedWhittaker.placeEmbed K v xv = UnramifiedWhittaker.placeEmbed K v xv * h₂ i)
    (x₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hxsum₂ : ∀ g, x₂ g = ∑ i, cs₂ i * rightConv K R₂.toFun f₂ (g * h₂ i))
    (_hxint₂ : ∀ (α' : K) (g : AdelicGL2 (𝓞 K) K), WhittakerCoefficientIntegrable K
      (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K))
      (NumberField.StandardAddChar.stdAddChar K) x₂ α' g)
    (_hxper₂ : ∀ (β : K) (uu : AdeleRing (𝓞 K) K) (hh : AdelicGL2 (𝓞 K) K),
      x₂ (unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β + uu) * hh) = x₂ (unipotentGL2 uu * hh))
    (_hxZ₂ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x₂ (centralScalar (𝓞 K) K z * g) = ((R₂.centralChar ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x₂ g)
    (v : HeightOneSpectrum (𝓞 K)) (_hv : v ∉ S)
    (k₁ k₂ : AdelicGL2 (𝓞 K) K) (_hk₁ : glFin (𝓞 K) K k₁ = 1) (_hk₂ : glFin (𝓞 K) K k₂ = 1)
    (g : AdelicGL2 (𝓞 K) K)
    (_hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2)
    (m : ℕ) :
    whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₁ 1 ((heckeGen (𝓞 K) K v) ^ m * g * k₁) *
        (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₂ 1 ((heckeGen (𝓞 K) K v) ^ m * g * k₂)) =
      UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) (Θ₁.toRawCentral.a v) (Θ₁.toRawCentral.b v) m *
        UnramifiedWhittaker.heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)
          ((starRingEnd ℂ) (Θ₂.toRawCentral.a v)) ((starRingEnd ℂ) (Θ₂.toRawCentral.b v)) m *
        (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₁ 1 (g * k₁) *
          (starRingEnd ℂ) (whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x₂ 1 (g * k₂))) := by sorry
