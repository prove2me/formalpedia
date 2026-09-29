-- Prove2me | Theorems.Thm_AutomorphicForm_CyclicBaseChangeLifting_exists_rayClassChar_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable_of_finrank_eq_three
-- name    : AutomorphicForm.CyclicBaseChangeLifting.exists_rayClassChar_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable_of_finrank_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/ccc0084a-500e-53c8-830d-58dcd5d99280
-- title:
--   Cubic base change: eigensystems differ by a ray-class twist
-- statement:
--   Let $E/F$ be an extension of number fields which is Galois with $[E:F]=3$. Fix reals $c_F,u_F,d_{1F},d_{2F}$ and a finite set $T_F$ of points of $\mathrm{GL}_2$ over the adeles of $F$, and likewise $c_E,u_E,d_{1E},d_{2E}$ and a finite $T_E$ over $E$; write $W_F=\bigcup_{x\in T_F}\,\mathfrak S_F(c_F,u_F,d_{1F},d_{2F})\,x$ and $W_E$ for the analogous union over $E$, where `centreCutSiegelSet` consists of the adelic matrices with integral finite part whose archimedean component at every infinite place has $\mathrm{localHeight}\ge c$, $\mathrm{xWindowSq}\le u^2$ and determinant norm in $[d_1,d_2]$. Assume $0<c_F$, $0<d_{1F}<d_{2F}$, $d_{1E}<d_{2E}$, and that each of $W_E$, $W_F$ meets every coset $\Gamma g Z$ modulo the image of the rational points and the adelic central scalars (`CoversModCentre`). Then for all Hecke eigensystems $\pi,\pi'$ over $F$ with complex values (a nonzero level ideal together with functions $a,b$ on the height-one spectrum of $\mathcal O_F$) which satisfy `IsArithGenuineCuspRealizable`, i.e. the eigensystem with $b$ rescaled to $(\mathrm{cNorm}\,v)^{-1}b(v)$ admits a genuine smooth cusp realisation at the carrier pins given by the Borel structure and Haar measure on adelic $\mathrm{GL}_2$, the region $W_F$, full central subgroup, level subgroups $N\mapsto \mathrm{levelOne}(N)\sqcap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}$, and the additive adelic Haar measure conditioned on the adelic box; and for every eigensystem $\Psi$ over $E$ which is such a realizable object for the corresponding pins over $W_E$ and is a base change of both $\pi$ and $\pi'$ (outside a finite set of primes $\mathfrak P$ of $E$ one has $\Psi.a\,\mathfrak P=\mathrm{satakePow}$ of the data of the eigensystem at the prime below with exponent the inertia degree, and $\Psi.b\,\mathfrak P=b^{f}$): there exist an ideal $\mathfrak f\subseteq\mathcal O_F$ with $\mathfrak f\ne 0$ and $v^{4e_2(v)+2e_3(v)+1}\mid\mathfrak f$ for every $v$ whose chosen prime above in $E$ has nontrivial inertia (`IsAdmissibleModulus`), and a homomorphism $\omega$ from the narrow ray class group of $F$ modulo $\mathfrak f$ to $\mathbb C^\times$, such that for every prime $w$ of $E$ whose prime $v=w\cap\mathcal O_F$ does not divide $\mathfrak f$ one has $\omega(\,[v]^{f(w/v)}\,)=1$, and there is a finite set $S$ of primes of $F$ with $\pi'.a\,v=\omega([v])\,\pi.a\,v$ and $\pi'.b\,v=\omega([v])^2\,\pi.b\,v$ for all $v\notin S$ not dividing $\mathfrak f$.
--
--   This is the cuspidal case of property (C) of cyclic base change for $\mathrm{GL}(2)$ in degree $3$: two cuspidal eigensystems over $F$ with a common base change to the cyclic cubic extension $E$ differ by a character of a narrow ray class group of $F$ which kills the relevant inertia-degree powers of prime classes. It feeds the comparison of such eigensystems with Artin–Frobenius data used in the Langlands–Tunnell input to modularity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CyclicBaseChangeLifting_exists_rayClassChar_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable_of_finrank_eq_three.lean

import Definitions.Def_AutomorphicForm_CyclicBaseChangeLifting
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open Deep.NTSupply LanglandsTunnell.P2.Artin

theorem AutomorphicForm.CyclicBaseChangeLifting.exists_rayClassChar_twist_of_isBaseChangeOf_of_isArithGenuineCuspRealizable_of_finrank_eq_three
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E]
    [IsGalois F E]
    (h3 : Module.finrank F E = 3)
    (cF uF d₁F d₂F : ℝ) (TF : Finset (AdelicGL2 (𝓞 F) F))
    (cE uE d₁E d₂E : ℝ) (TE : Finset (AdelicGL2 (𝓞 E) E))
    (hcF : 0 < cF) (hd₁F : 0 < d₁F) (hdF : d₁F < d₂F)
    (hdE : d₁E < d₂E)
    (hcovE : CoversModCentre E (⋃ x ∈ TE, (· * x) '' centreCutSiegelSet E cE uE d₁E d₂E))
    (hcovF : CoversModCentre F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)) :
    ∀ π π' : HeckeEigensystem F ℂ,
      (IsArithGenuineCuspRealizable F
            (productionPinsOf F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)) π) →
      (IsArithGenuineCuspRealizable F
            (productionPinsOf F (⋃ x ∈ TF, (· * x) '' centreCutSiegelSet F cF uF d₁F d₂F)
              (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
              (adelicBox F)) π') →
      ∀ Ψ : HeckeEigensystem E ℂ, IsBaseChangeOf π Ψ → IsBaseChangeOf π' Ψ →
      (IsArithGenuineCuspRealizable E
            (productionPinsOf E (⋃ x ∈ TE, (· * x) '' centreCutSiegelSet E cE uE d₁E d₂E)
              (fun N => levelOne (𝓞 E) E N ⊓ finiteAdelicGL2Subgroup E) (fun v => heckeGen (𝓞 E) E v)
              (adelicBox E)) Ψ) →
      ∃ 𝔣 : Ideal (𝓞 F), IsAdmissibleModulus F E 𝔣 ∧
        ∃ ω : NarrowRayClassGroup F 𝔣 →* ℂˣ,
          (∀ (w : HeightOneSpectrum (𝓞 E)) (hw : ¬ ((w.under (𝓞 F)).asIdeal ∣ 𝔣)),
            ω (primeClass F 𝔣 (w.under (𝓞 F)) hw ^
              ((w.under (𝓞 F)).asIdeal.inertiaDeg' w.asIdeal)) = 1) ∧
          ∃ S : Finset (HeightOneSpectrum (𝓞 F)),
            ∀ v ∉ S, ∀ (hv : ¬ v.asIdeal ∣ 𝔣),
              π'.a v = (ω (primeClass F 𝔣 v hv) : ℂ) * π.a v ∧
              π'.b v = (ω (primeClass F 𝔣 v hv) : ℂ) ^ 2 * π.b v := by sorry
