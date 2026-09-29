-- Prove2me | Theorems.Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
-- name    : AutomorphicForm.integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/7acb1022-9add-5570-abd7-b91a8a4a5bec
-- title:
--   Hecke words extracted from int f·(χ∘det)
-- statement:
--   Let $K$ be a number field and let $SK$, $T$ be finite sets of finite places of $K$ with $T$ disjoint from $SK$. For every finite place $v$ fix an element $\varpi_v$ of the valuation ring of the completion $K_v$, required for $v\in T$ to be irreducible and to have nonzero image in $K_v$; fix natural numbers $n_v$ and elements $r_{v,1},\dots,r_{v,n_v}$ of $GL_2(K_v)$ which for $v\in T$ form a Hecke coset system for the subgroup $U_v$ of $GL_2(K_v)$ that is the image of $GL_2$ of the valuation ring and the element $\mathrm{diag}(\varpi_v,1)$: each $r_{v,i}$ lies in the double coset $U_v\,\mathrm{diag}(\varpi_v,1)\,U_v$, every element of that double coset lies in some left coset $r_{v,i}U_v$, and these cosets are pairwise distinct. Fix $z_v\in GL_2(K_v)$ which for $v\in T$ is the scalar matrix $\varpi_v\cdot 1$, exponents $k_v,j_v\in\mathbb N$, a function $f_\infty$ on $GL_2$ of the infinite adeles, functions $f_v$ on $GL_2(K_v)$, a continuous compactly supported $f$ on $GL_2(\mathbb A_K)$ and a function $f_{\mathrm{fin}}$ on $GL_2$ of the finite adeles. The hypothesis `IsUnitFactorization` at $SK\cup T$ asserts: $f_\infty$ is a compactly supported function given by a smooth function of the archimedean matrix entries; $f_{\mathrm{fin}}$ is locally constant with compact support; at each $v\in SK\cup T$ the prescribed local factor — namely $f_v$ for $v\notin T$, and for $v\in T$ the Hecke word
--   $$x\mapsto \sum_{\iota\colon \mathrm{Fin}\,k_v\to \mathrm{Fin}\,n_v}\mathbf 1_{\Omega_v}\bigl((r_{v,\iota(0)}\cdots r_{v,\iota(k_v-1)}\,z_v^{\,j_v})^{-1}x\bigr),$$
--   where $\Omega_v$ is the set of $x\in GL_2(K_v)$ with both $x$ and $x^{-1}$ having entries in the valuation ring — is locally constant with compact support; $f_{\mathrm{fin}}(h)=\prod_{v\in SK\cup T}(\text{local factor})(h_v)$ whenever $h_w\in\Omega_w$ for all $w\notin SK\cup T$, and $f_{\mathrm{fin}}(h)=0$ if $h_w\notin\Omega_w$ for some $w\notin SK\cup T$; and $f(g)=f_\infty(g_\infty)f_{\mathrm{fin}}(g_{\mathrm{fin}})$. Finally let $\chi\colon\mathbb A_K^\times\to\mathbb C^\times$ be a homomorphism which for each $v\in T$ satisfies $\chi(t)=1$ for every $t\in K_v^\times$, embedded as an idele, with $t$ and $t^{-1}$ in the valuation ring. Then, for the Haar measure `adelicGLHaar` on $GL_2(\mathbb A_K)$,
--   $$\int f(g)\,\chi(\det g)\,dg=\prod_{v\in T}\Bigl((N(v)+1)\chi(\det \mathrm{hg}_v)\Bigr)^{k_v}\Bigl(N(v)^{-1}\bigl(N(v)\,\chi(\det \mathrm{hg}_v)^2\bigr)\Bigr)^{j_v}\cdot\int f_0(g)\,\chi(\det g)\,dg,$$
--   where $N(v)$ is the absolute norm of the prime $v$ viewed in $\mathbb C$, $\mathrm{hg}_v$ is the adelic Hecke generator `heckeGen` at $v$, and $f_0$ is the indicator of $\{g:\ g_w\in\Omega_w \text{ for all } w\notin SK\}$ times $g\mapsto f_\infty(g_\infty)\prod_{v\in SK}f_v(g_v)$.
--
--   This is the one-dimensional (abelian) instance of the Hecke-word evaluation rules: the function $\chi\circ\det$ is an eigenfunction of the Hecke operator at $v$ with eigenvalue $(N(v)+1)\chi(\varpi_v)$, and of central translation by $\varpi_v$ with eigenvalue $\chi(\varpi_v)^2$, so that a word in Hecke and central operators inserted at the places of $T$ contributes only a scalar to the adelic integral. It is used in the construction of atomic forms and in the convergence statement for truncated integrals of $\chi\circ\det$-twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integral_mul_chiDet_eq_prod_pow_mul_pow_mul_integral_mul_chiDet_of_isUnitFactorization
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (SK T : Finset (HeightOneSpectrum (𝓞 K))) (hTd : Disjoint T SK)
    (ϖKs : ∀ v : HeightOneSpectrum (𝓞 K), v.adicCompletionIntegers K)
    (hirr : ∀ v ∈ T, Irreducible (ϖKs v))
    (hϖKs0 : ∀ v ∈ T, algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) ≠ 0)
    (nKs : HeightOneSpectrum (𝓞 K) → ℕ)
    (rKs : ∀ v : HeightOneSpectrum (𝓞 K), Fin (nKs v) → GL (Fin 2) (v.adicCompletion K))
    (hcos : ∀ (v : HeightOneSpectrum (𝓞 K)) (hv : v ∈ T),
      HeckeIntegralSeam.IsHeckeCosetSystem
        (LocalGL2.integralSubgroup (v.adicCompletionIntegers K) (v.adicCompletion K))
        (LocalGL2.diagPi (ϖKs v) (hϖKs0 v hv)) (rKs v))
    (zKs : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K))
    (hzKs : ∀ v ∈ T, (zKs v : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (ϖKs v) •
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (ks js : HeightOneSpectrum (𝓞 K) → ℕ)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (hfact : IsUnitFactorization K (SK ∪ T) f faK ff
      (fun v => if v ∈ T then fun x : GL (Fin 2) (v.adicCompletion K) =>
        ∑ ι : Fin (ks v) → Fin (nKs v),
          (localIntegralSet K v).indicator (fun _ => (1 : ℂ))
            (((List.ofFn fun m => rKs v (ι m)).prod * zKs v ^ js v)⁻¹ * x)
        else fSK v))
    (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (hχ : ∀ v ∈ T, NumberField.TateGlobal.IsUnramifiedCharAt χ v) :
    ∫ g, f g * chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      (∏ v ∈ T,
        (((HeckeEigensystem.cNorm v) + 1) *
            ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ)) ^ ks v *
          ((HeckeEigensystem.cNorm v)⁻¹ *
            ((HeckeEigensystem.cNorm v) *
              ((χ (Matrix.GeneralLinearGroup.det (heckeGen (𝓞 K) K v)) : ℂˣ) : ℂ) ^ 2)) ^ js v) *
        ∫ g, {g : AdelicGL2 (𝓞 K) K |
              ∀ v ∉ SK, AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g) ∈
                localIntegralSet K v}.indicator
            (fun g => faK (AdelicLevel.glArch (𝓞 K) K g) *
              ∏ v ∈ SK, fSK v (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K g))) g *
          chiDet (𝓞 K) K χ g ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by sorry
